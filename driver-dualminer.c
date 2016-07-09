/*
 * Copyright 2012-2013 Andrew Smith
 * Copyright 2012 Xiangfu <xiangfu@openmobilefree.com>
 * Copyright 2013-2014 Con Kolivas <kernel@kolivas.org>
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 3 of the License, or (at your option)
 * any later version.  See COPYING for more details.
 */

/*
 * Those code should be works fine with V2 and V3 bitstream of Icarus.
 * Operation:
 *   No detection implement.
 *   Input: 64B = 32B midstate + 20B fill bytes + last 12 bytes of block head.
 *   Return: send back 32bits immediately when Icarus found a valid nonce.
 *           no query protocol implemented here, if no data send back in ~11.3
 *           seconds (full cover time on 32bit nonce range by 380MH/s speed)
 *           just send another work.
 * Notice:
 *   1. Icarus will start calculate when you push a work to them, even they
 *      are busy.
 *   2. The 2 FPGAs on Icarus will distribute the job, one will calculate the
 *      0 ~ 7FFFFFFF, another one will cover the 80000000 ~ FFFFFFFF.
 *   3. It's possible for 2 FPGAs both find valid nonce in the meantime, the 2
 *      valid nonce will all be send back.
 *   4. Icarus will stop work when: a valid nonce has been found or 32 bits
 *      nonce range is completely calculated.
 */


#include <float.h>
#include <limits.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <strings.h>
#include <sys/time.h>
#include <unistd.h>
#include <math.h>

#include "config.h"

#ifdef WIN32
#include <windows.h>
#endif

#include "compat.h"
#include "miner.h"
#include "usbutils.h"

// The serial I/O speed - Linux uses a define 'B115200' in bits/termios.h
#define DUALMINER_IO_SPEED 115200

#define DUALMINER_BUF_SIZE 8
// The size of a successful nonce read
#define ANT_READ_SIZE 5
#define DUALMINER_READ_SIZE 4

// Ensure the sizes are correct for the Serial read
#if (DUALMINER_READ_SIZE != 4)
#error DUALMINER_READ_SIZE must be 4
#endif
#define ASSERT1(condition) __maybe_unused static char sizeof_uint32_t_must_be_4[(condition)?1:-1]
ASSERT1(sizeof(uint32_t) == 4);

// TODO: USB? Different calculation? - see usbstats to work it out e.g. 1/2 of normal send time
//  or even use that number? 1/2
// #define DUALMINER_READ_TIME(baud) ((double)DUALMINER_READ_SIZE * (double)8.0 / (double)(baud))
// maybe 1ms?
#define DUALMINER_READ_TIME(baud) (0.001)

// USB ms timeout to wait - user specified timeouts are multiples of this
#define DUALMINER_WAIT_TIMEOUT 100
#define ANT_WAIT_TIMEOUT 10
#define DUALMINER_CMR2_TIMEOUT 1

// Defined in multiples of DUALMINER_WAIT_TIMEOUT
// Must of course be greater than DUALMINER_READ_COUNT_TIMING/DUALMINER_WAIT_TIMEOUT
// There's no need to have this bigger, since the overhead/latency of extra work
// is pretty small once you get beyond a 10s nonce range time and 10s also
// means that nothing slower than 429MH/s can go idle so most dualminer devices
// will always mine without idling
#define DUALMINER_READ_TIME_LIMIT_MAX 100

// In timing mode: Default starting value until an estimate can be obtained
// 5000 ms allows for up to a ~840MH/s device
#define DUALMINER_READ_COUNT_TIMING	5000

// Antminer USB is > 1GH/s so use a shorter limit
// 1000 ms allows for up to ~4GH/s device
#define ANTUSB_READ_COUNT_TIMING	1000

#define DUALMINER_READ_COUNT_MIN		DUALMINER_WAIT_TIMEOUT
#define SECTOMS(s)	((int)((s) * 1000))
// How many ms below the expected completion time to abort work
// extra in case the last read is delayed
#define DUALMINER_READ_REDUCE	((int)(DUALMINER_WAIT_TIMEOUT * 1.5))

// For a standard Icarus REV3 (to 5 places)
// Since this rounds up a the last digit - it is a slight overestimate
// Thus the hash rate will be a VERY slight underestimate
// (by a lot less than the displayed accuracy)
// Minor inaccuracy of these numbers doesn't affect the work done,
// only the displayed MH/s
#define DUALMINER_REV3_HASH_TIME 0.0000000026316
#define LANCELOT_HASH_TIME 0.0000000025000
#define ASICMINERUSB_HASH_TIME 0.0000000029761
// TODO: What is it?
#define CAIRNSMORE1_HASH_TIME 0.0000000027000
// Per FPGA
#define CAIRNSMORE2_HASH_TIME 0.0000000066600
#define NANOSEC 1000000000.0
#define ANTMINERUSB_HASH_MHZ  0.000000125
#define ANTMINERUSB_HASH_TIME (ANTMINERUSB_HASH_MHZ / (double)(opt_anu_freq))
#define CAIRNSMORE2_INTS 4

// Icarus Rev3 doesn't send a completion message when it finishes
// the full nonce range, so to avoid being idle we must abort the
// work (by starting a new work item) shortly before it finishes
//
// Thus we need to estimate 2 things:
//	1) How many hashes were done if the work was aborted
//	2) How high can the timeout be before the Icarus is idle,
//		to minimise the number of work items started
//	We set 2) to 'the calculated estimate' - DUALMINER_READ_REDUCE
//	to ensure the estimate ends before idle
//
// The simple calculation used is:
//	Tn = Total time in seconds to calculate n hashes
//	Hs = seconds per hash
//	Xn = number of hashes
//	W  = code/usb overhead per work
//
// Rough but reasonable estimate:
//	Tn = Hs * Xn + W	(of the form y = mx + b)
//
// Thus:
//	Line of best fit (using least squares)
//
//	Hs = (n*Sum(XiTi)-Sum(Xi)*Sum(Ti))/(n*Sum(Xi^2)-Sum(Xi)^2)
//	W = Sum(Ti)/n - (Hs*Sum(Xi))/n
//
// N.B. W is less when aborting work since we aren't waiting for the reply
//	to be transferred back (DUALMINER_READ_TIME)
//	Calculating the hashes aborted at n seconds is thus just n/Hs
//	(though this is still a slight overestimate due to code delays)
//

// Both below must be exceeded to complete a set of data
// Minimum how long after the first, the last data point must be
#define HISTORY_SEC 60
// Minimum how many points a single DUALMINER_HISTORY should have
#define MIN_DATA_COUNT 5
// The value MIN_DATA_COUNT used is doubled each history until it exceeds:
#define MAX_MIN_DATA_COUNT 100

static struct timeval history_sec = { HISTORY_SEC, 0 };

// Store the last INFO_HISTORY data sets
// [0] = current data, not yet ready to be included as an estimate
// Each new data set throws the last old set off the end thus
// keeping a ongoing average of recent data
#define INFO_HISTORY 10

struct DUALMINER_HISTORY {
	struct timeval finish;
	double sumXiTi;
	double sumXi;
	double sumTi;
	double sumXi2;
	uint32_t values;
	uint32_t hash_count_min;
	uint32_t hash_count_max;
};

enum timing_mode { MODE_DEFAULT, MODE_SHORT, MODE_LONG, MODE_VALUE };

static const char *MODE_DEFAULT_STR = "default";
static const char *MODE_SHORT_STR = "short";
static const char *MODE_SHORT_STREQ = "short=";
static const char *MODE_LONG_STR = "long";
static const char *MODE_LONG_STREQ = "long=";
static const char *MODE_VALUE_STR = "value";
static const char *MODE_UNKNOWN_STR = "unknown";

struct DUALMINER_INFO {
	enum sub_ident ident;
	int intinfo;

	// time to calculate the golden_ob
	uint64_t golden_hashes;
	struct timeval golden_tv;

	struct DUALMINER_HISTORY history[INFO_HISTORY+1];
	uint32_t min_data_count;

	int timeout;

	// seconds per Hash
	double Hs;
	// ms til we abort
	int read_time;
	// ms limit for (short=/long=) read_time
	int read_time_limit;
	// How long without hashes is considered a failed device
	int fail_time;

	enum timing_mode timing_mode;
	bool do_dualminer_timing;

	double fullnonce;
	int count;
	double W;
	uint32_t values;
	uint64_t hash_count_range;

	// Determine the cost of history processing
	// (which will only affect W)
	uint64_t history_count;
	struct timeval history_time;

	// dualminer-options
	int baud;
	int work_division;
	int fpga_count;
	uint32_t nonce_mask;

	uint8_t cmr2_speed;
	bool speed_next_work;
	bool flash_next_work;

	int nonce_size;

	bool failing;
};

#define DUALMINER_MIDSTATE_SIZE 32
#define DUALMINER_UNUSED_SIZE 16
#define DUALMINER_WORK_SIZE 12

#define DUALMINER_WORK_DATA_OFFSET 64

#define DUALMINER_CMR2_SPEED_FACTOR 2.5
#define DUALMINER_CMR2_SPEED_MIN_INT 100
#define DUALMINER_CMR2_SPEED_DEF_INT 180
#define DUALMINER_CMR2_SPEED_MAX_INT 220
#define CMR2_INT_TO_SPEED(_speed) ((uint8_t)((float)_speed / DUALMINER_CMR2_SPEED_FACTOR))
#define DUALMINER_CMR2_SPEED_MIN CMR2_INT_TO_SPEED(DUALMINER_CMR2_SPEED_MIN_INT)
#define DUALMINER_CMR2_SPEED_DEF CMR2_INT_TO_SPEED(DUALMINER_CMR2_SPEED_DEF_INT)
#define DUALMINER_CMR2_SPEED_MAX CMR2_INT_TO_SPEED(DUALMINER_CMR2_SPEED_MAX_INT)
#define DUALMINER_CMR2_SPEED_INC 1
#define DUALMINER_CMR2_SPEED_DEC -1
#define DUALMINER_CMR2_SPEED_FAIL -10

#define DUALMINER_CMR2_PREFIX ((uint8_t)0xB7)
#define DUALMINER_CMR2_CMD_SPEED ((uint8_t)0)
#define DUALMINER_CMR2_CMD_FLASH ((uint8_t)1)
#define DUALMINER_CMR2_DATA_FLASH_OFF ((uint8_t)0)
#define DUALMINER_CMR2_DATA_FLASH_ON ((uint8_t)1)
#define DUALMINER_CMR2_CHECK ((uint8_t)0x6D)

struct DUALMINER_WORK {
	uint8_t midstate[DUALMINER_MIDSTATE_SIZE];
	// These 4 bytes are for CMR2 bitstreams that handle MHz adjustment
	uint8_t check;
	uint8_t data;
	uint8_t cmd;
	uint8_t prefix;
	uint8_t unused[DUALMINER_UNUSED_SIZE];
	uint8_t work[DUALMINER_WORK_SIZE];
};

#define END_CONDITION 0x0000ffff

// Looking for options in --dualminer-timing and --dualminer-options:
//
// Code increments this each time we start to look at a device
// However, this means that if other devices are checked by
// the Icarus code (e.g. Avalon only as at 20130517)
// they will count in the option offset
//
// This, however, is deterministic so that's OK
//
// If we were to increment after successfully finding an Icarus
// that would be random since an Icarus may fail and thus we'd
// not be able to predict the option order
//
// Devices are checked in the order libusb finds them which is ?
//
static int option_offset = -1;

/*
#define ICA_BUFSIZ (0x200)

static void transfer_read(struct cgpu_info *dualminer, uint8_t request_type, uint8_t bRequest, uint16_t wValue, uint16_t wIndex, char *buf, int bufsiz, int *amount, enum usb_cmds cmd)
{
	int err;

	err = usb_transfer_read(dualminer, request_type, bRequest, wValue, wIndex, buf, bufsiz, amount, cmd);

	applog(LOG_DEBUG, "%s: cgid %d %s got err %d",
			dualminer->drv->name, dualminer->cgminer_id,
			usb_cmdname(cmd), err);
}
*/

static void _transfer(struct cgpu_info *dualminer, uint8_t request_type, uint8_t bRequest, uint16_t wValue, uint16_t wIndex, uint32_t *data, int siz, enum usb_cmds cmd)
{
	int err;

	err = usb_transfer_data(dualminer, request_type, bRequest, wValue, wIndex, data, siz, cmd);

	applog(LOG_DEBUG, "%s: cgid %d %s got err %d",
			dualminer->drv->name, dualminer->cgminer_id,
			usb_cmdname(cmd), err);
}

#define transfer(dualminer, request_type, bRequest, wValue, wIndex, cmd) \
		_transfer(dualminer, request_type, bRequest, wValue, wIndex, NULL, 0, cmd)

static void dualminer_initialise(struct cgpu_info *dualminer, int baud)
{
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(dualminer->device_data);
	uint16_t wValue, wIndex;
	enum sub_ident ident;
	int interface;

	if (dualminer->usbinfo.nodev)
		return;

	interface = _usb_interface(dualminer, info->intinfo);
	ident = usb_ident(dualminer);

	switch (ident) {
		case IDENT_BLT:
		case IDENT_LLT:
		case IDENT_CMR1:
		case IDENT_CMR2:
			// Reset
			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_RESET,
				 interface, C_RESET);

			if (dualminer->usbinfo.nodev)
				return;

			// Latency
			_usb_ftdi_set_latency(dualminer, info->intinfo);

			if (dualminer->usbinfo.nodev)
				return;

			// Set data control
			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_DATA, FTDI_VALUE_DATA_BLT,
				 interface, C_SETDATA);

			if (dualminer->usbinfo.nodev)
				return;

			// default to BLT/LLT 115200
			wValue = FTDI_VALUE_BAUD_BLT;
			wIndex = FTDI_INDEX_BAUD_BLT;

			if (ident == IDENT_CMR1 || ident == IDENT_CMR2) {
				switch (baud) {
					case 115200:
						wValue = FTDI_VALUE_BAUD_CMR_115;
						wIndex = FTDI_INDEX_BAUD_CMR_115;
						break;
					case 57600:
						wValue = FTDI_VALUE_BAUD_CMR_57;
						wIndex = FTDI_INDEX_BAUD_CMR_57;
						break;
					default:
						quit(1, "dualminer_intialise() invalid baud (%d) for Cairnsmore1", baud);
						break;
				}
			}

			// Set the baud
			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_BAUD, wValue,
				 (wIndex & 0xff00) | interface, C_SETBAUD);

			if (dualminer->usbinfo.nodev)
				return;

			// Set Modem Control
			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_MODEM, FTDI_VALUE_MODEM,
				 interface, C_SETMODEM);

			if (dualminer->usbinfo.nodev)
				return;

			// Set Flow Control
			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_FLOW, FTDI_VALUE_FLOW,
				 interface, C_SETFLOW);

			if (dualminer->usbinfo.nodev)
				return;

			// Clear any sent data
			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_PURGE_TX,
				 interface, C_PURGETX);

			if (dualminer->usbinfo.nodev)
				return;

			// Clear any received data
			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_PURGE_RX,
				 interface, C_PURGERX);
			break;
		case IDENT_DM:
			// Set Data Control
			transfer(dualminer, PL2303_CTRL_OUT, PL2303_REQUEST_CTRL, PL2303_VALUE_CTRL,
				 interface, C_SETDATA);

			if (dualminer->usbinfo.nodev)
				return;

			// Set Line Control
			uint32_t ica_data[2] = { PL2303_VALUE_LINE0, PL2303_VALUE_LINE1 };
			_transfer(dualminer, PL2303_CTRL_OUT, PL2303_REQUEST_LINE, PL2303_VALUE_LINE,
				 interface, &ica_data[0], PL2303_VALUE_LINE_SIZE, C_SETLINE);

			if (dualminer->usbinfo.nodev)
				return;

			// Vendor
			transfer(dualminer, PL2303_VENDOR_OUT, PL2303_REQUEST_VENDOR, PL2303_VALUE_VENDOR,
				 interface, C_VENDOR);
			break;
		case IDENT_AMU:
		case IDENT_ANU:
			// Enable the UART
			transfer(dualminer, CP210X_TYPE_OUT, CP210X_REQUEST_IFC_ENABLE,
				 CP210X_VALUE_UART_ENABLE,
				 interface, C_ENABLE_UART);

			if (dualminer->usbinfo.nodev)
				return;

			// Set data control
			transfer(dualminer, CP210X_TYPE_OUT, CP210X_REQUEST_DATA, CP210X_VALUE_DATA,
				 interface, C_SETDATA);

			if (dualminer->usbinfo.nodev)
				return;

			// Set the baud
			uint32_t data = CP210X_DATA_BAUD;
			_transfer(dualminer, CP210X_TYPE_OUT, CP210X_REQUEST_BAUD, 0,
				 interface, &data, sizeof(data), C_SETBAUD);
			break;
		default:
			quit(1, "dualminer_intialise() called with invalid %s cgid %i ident=%d",
				dualminer->drv->name, dualminer->cgminer_id, ident);
	}
}

static void rev(unsigned char *s, size_t l)
{
	size_t i, j;
	unsigned char t;

	for (i = 0, j = l - 1; i < j; i++, j--) {
		t = s[i];
		s[i] = s[j];
		s[j] = t;
	}
}

#define ICA_NONCE_ERROR -1
#define ICA_NONCE_OK 0
#define ICA_NONCE_RESTART 1
#define ICA_NONCE_TIMEOUT 2

static int dualminer_get_nonce(struct cgpu_info *dualminer, unsigned char *buf, struct timeval *tv_start,
			    struct timeval *tv_finish, struct thr_info *thr, int read_time)
{
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(dualminer->device_data);
	int err, amt, rc;

	if (dualminer->usbinfo.nodev)
		return ICA_NONCE_ERROR;

	cgtime(tv_start);
	err = usb_read_ii_timeout_cancellable(dualminer, info->intinfo, (char *)buf,
					      info->nonce_size, &amt, read_time,
					      C_GETRESULTS);
	cgtime(tv_finish);

	if (err < 0 && err != LIBUSB_ERROR_TIMEOUT) {
		applog(LOG_ERR, "%s%i: Comms error (rerr=%d amt=%d)", dualminer->drv->name,
		       dualminer->device_id, err, amt);
		dev_error(dualminer, REASON_DEV_COMMS_ERROR);
		return DM_NONCE_ERROR;
	}

	if (amt >= DUALMINER_READ_SIZE)
		return DM_NONCE_OK;

	rc = SECTOMS(tdiff(tv_finish, tv_start));
	if (thr && thr->work_restart) {
		applog(LOG_DEBUG, "Icarus Read: Work restart at %d ms", rc);
		return DM_NONCE_RESTART;
	}

	if (amt > 0)
		applog(LOG_DEBUG, "Icarus Read: Timeout reading for %d ms", rc);
	else
		applog(LOG_DEBUG, "Icarus Read: No data for %d ms", rc);
	return DM_NONCE_TIMEOUT;
}


static const char *timing_mode_str(enum timing_mode timing_mode)
{
	switch(timing_mode) {
	case MODE_DEFAULT:
		return MODE_DEFAULT_STR;
	case MODE_SHORT:
		return MODE_SHORT_STR;
	case MODE_LONG:
		return MODE_LONG_STR;
	case MODE_VALUE:
		return MODE_VALUE_STR;
	default:
		return MODE_UNKNOWN_STR;
	}
}

static void set_timing_mode(int this_option_offset, struct cgpu_info *dualminer)
{
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(dualminer->device_data);
	int read_count_timing = 0;
	enum sub_ident ident;
	double Hs, fail_time;
	char buf[BUFSIZ+1];
	char *ptr, *comma, *eq;
	size_t max;
	int i;

	if (opt_dualminer_timing == NULL)
		buf[0] = '\0';
	else {
		ptr = opt_dualminer_timing;
		for (i = 0; i < this_option_offset; i++) {
			comma = strchr(ptr, ',');
			if (comma == NULL)
				break;
			ptr = comma + 1;
		}

		comma = strchr(ptr, ',');
		if (comma == NULL)
			max = strlen(ptr);
		else
			max = comma - ptr;

		if (max > BUFSIZ)
			max = BUFSIZ;
		strncpy(buf, ptr, max);
		buf[max] = '\0';
	}

	ident = usb_ident(dualminer);
	switch (ident) {
		case IDENT_DM:
			info->Hs = DUALMINER_REV3_HASH_TIME;
			read_count_timing = DUALMINER_READ_COUNT_TIMING;
			break;
		default:
			quit(1, "Icarus get_options() called with invalid %s ident=%d",
				dualminer->drv->name, ident);
	}

	info->read_time = 0;
	info->read_time_limit = 0; // 0 = no limit

	if (strcasecmp(buf, MODE_SHORT_STR) == 0) {
		// short
		info->read_time = read_count_timing;

		info->timing_mode = MODE_SHORT;
		info->do_dualminer_timing = true;
	} else if (strncasecmp(buf, MODE_SHORT_STREQ, strlen(MODE_SHORT_STREQ)) == 0) {
		// short=limit
		info->read_time = read_count_timing;

		info->timing_mode = MODE_SHORT;
		info->do_dualminer_timing = true;

		info->read_time_limit = atoi(&buf[strlen(MODE_SHORT_STREQ)]);
		if (info->read_time_limit < 0)
			info->read_time_limit = 0;
		if (info->read_time_limit > DUALMINER_READ_TIME_LIMIT_MAX)
			info->read_time_limit = DUALMINER_READ_TIME_LIMIT_MAX;
	} else if (strcasecmp(buf, MODE_LONG_STR) == 0) {
		// long
		info->read_time = read_count_timing;

		info->timing_mode = MODE_LONG;
		info->do_dualminer_timing = true;
	} else if (strncasecmp(buf, MODE_LONG_STREQ, strlen(MODE_LONG_STREQ)) == 0) {
		// long=limit
		info->read_time = read_count_timing;

		info->timing_mode = MODE_LONG;
		info->do_dualminer_timing = true;

		info->read_time_limit = atoi(&buf[strlen(MODE_LONG_STREQ)]);
		if (info->read_time_limit < 0)
			info->read_time_limit = 0;
		if (info->read_time_limit > DUALMINER_READ_TIME_LIMIT_MAX)
			info->read_time_limit = DUALMINER_READ_TIME_LIMIT_MAX;
	} else if ((Hs = atof(buf)) != 0) {
		// ns[=read_time]
		info->Hs = Hs / NANOSEC;
		info->fullnonce = info->Hs * (((double)0xffffffff) + 1);

		if ((eq = strchr(buf, '=')) != NULL)
			info->read_time = atoi(eq+1) * DUALMINER_WAIT_TIMEOUT;

		if (info->read_time < DUALMINER_READ_COUNT_MIN)
			info->read_time = SECTOMS(info->fullnonce) - DUALMINER_READ_REDUCE;

		if (unlikely(info->read_time < DUALMINER_READ_COUNT_MIN))
			info->read_time = DUALMINER_READ_COUNT_MIN;

		info->timing_mode = MODE_VALUE;
		info->do_dualminer_timing = false;
	} else {
		// Anything else in buf just uses DEFAULT mode

		info->fullnonce = info->Hs * (((double)0xffffffff) + 1);

		if ((eq = strchr(buf, '=')) != NULL)
			info->read_time = atoi(eq+1) * DUALMINER_WAIT_TIMEOUT;

		if (info->read_time < DUALMINER_READ_COUNT_MIN)
			info->read_time = SECTOMS(info->fullnonce) - DUALMINER_READ_REDUCE;

		if (unlikely(info->read_time < DUALMINER_READ_COUNT_MIN))
			info->read_time = DUALMINER_READ_COUNT_MIN;

		info->timing_mode = MODE_DEFAULT;
		info->do_dualminer_timing = false;
	}

	info->min_data_count = MIN_DATA_COUNT;

	// All values are in multiples of DUALMINER_WAIT_TIMEOUT
	info->read_time_limit *= DUALMINER_WAIT_TIMEOUT;

	applog(LOG_DEBUG, "%s: cgid %d Init: mode=%s read_time=%dms limit=%dms Hs=%e",
			dualminer->drv->name, dualminer->cgminer_id,
			timing_mode_str(info->timing_mode),
			info->read_time, info->read_time_limit, info->Hs);

	/* Set the time to detect a dead device to 25 full nonce ranges. */
	fail_time = info->Hs * 0xffffffffull * 25.0;
	/* Integer accuracy is definitely enough. */
	info->fail_time = fail_time;
}

static uint32_t mask(int work_division)
{
	uint32_t nonce_mask = 0x7fffffff;

	// yes we can calculate these, but this way it's easy to see what they are
	switch (work_division) {
	case 1:
		nonce_mask = 0xffffffff;
		break;
	case 2:
		nonce_mask = 0x7fffffff;
		break;
	case 4:
		nonce_mask = 0x3fffffff;
		break;
	case 8:
		nonce_mask = 0x1fffffff;
		break;
	default:
		quit(1, "Invalid2 dualminer-options for work_division (%d) must be 1, 2, 4 or 8", work_division);
	}

	return nonce_mask;
}

static void get_options(int this_option_offset, struct cgpu_info *dualminer, int *baud, int *work_division, int *fpga_count)
{
	char buf[BUFSIZ+1];
	char *ptr, *comma, *colon, *colon2;
	enum sub_ident ident;
	size_t max;
	int i, tmp;

	if (opt_dualminer_options == NULL)
		buf[0] = '\0';
	else {
		ptr = opt_dualminer_options;
		for (i = 0; i < this_option_offset; i++) {
			comma = strchr(ptr, ',');
			if (comma == NULL)
				break;
			ptr = comma + 1;
		}

		comma = strchr(ptr, ',');
		if (comma == NULL)
			max = strlen(ptr);
		else
			max = comma - ptr;

		if (max > BUFSIZ)
			max = BUFSIZ;
		strncpy(buf, ptr, max);
		buf[max] = '\0';
	}

	ident = usb_ident(dualminer);
	switch (ident) {
		case IDENT_ICA:
		default:
			quit(1, "Icarus get_options() called with invalid %s ident=%d",
				dualminer->drv->name, ident);
	}

	if (*buf) {
		colon = strchr(buf, ':');
		if (colon)
			*(colon++) = '\0';

		if (*buf) {
			tmp = atoi(buf);
			switch (tmp) {
			case 115200:
				*baud = 115200;
				break;
			case 57600:
				*baud = 57600;
				break;
			default:
				quit(1, "Invalid dualminer-options for baud (%s) must be 115200 or 57600", buf);
			}
		}

		if (colon && *colon) {
			colon2 = strchr(colon, ':');
			if (colon2)
				*(colon2++) = '\0';

			if (*colon) {
				tmp = atoi(colon);
				if (tmp == 1 || tmp == 2 || tmp == 4 || tmp == 8) {
					*work_division = tmp;
					*fpga_count = tmp;	// default to the same
				} else {
					quit(1, "Invalid dualminer-options for work_division (%s) must be 1, 2, 4 or 8", colon);
				}
			}

			if (colon2 && *colon2) {
				tmp = atoi(colon2);
				if (tmp > 0 && tmp <= *work_division)
					*fpga_count = tmp;
				else {
					quit(1, "Invalid dualminer-options for fpga_count (%s) must be >0 and <=work_division (%d)", colon2, *work_division);
				}
			}
		}
	}
}

unsigned char crc5(unsigned char *ptr, unsigned char len)
{
	unsigned char i, j, k;
	unsigned char crc = 0x1f;

	unsigned char crcin[5] = {1, 1, 1, 1, 1};
	unsigned char crcout[5] = {1, 1, 1, 1, 1};
	unsigned char din = 0;

	j = 0x80;
	k = 0;
	for (i = 0; i < len; i++) {
		if (*ptr & j)
			din = 1;
		else
			din = 0;
		crcout[0] = crcin[4] ^ din;
		crcout[1] = crcin[0];
		crcout[2] = crcin[1] ^ crcin[4] ^ din;
		crcout[3] = crcin[2];
		crcout[4] = crcin[3];

		j = j >> 1;
		k++;
		if (k == 8) {
			j = 0x80;
			k = 0;
			ptr++;
		}
		memcpy(crcin, crcout, 5);
	}
	crc = 0;
	if(crcin[4])
		crc |= 0x10;
	if(crcin[3])
		crc |= 0x08;
	if(crcin[2])
		crc |= 0x04;
	if(crcin[1])
		crc |= 0x02;
	if(crcin[0])
		crc |= 0x01;
	return crc;
}



static struct cgpu_info *dualminer_detect_one(struct libusb_device *dev, struct usb_find_devices *found)
{
	int this_option_offset = ++option_offset;
	struct DUALMINER_INFO *info;
	struct timeval tv_start, tv_finish;

	// Block 171874 nonce = (0xa2870100) = 0x000187a2
	// N.B. golden_ob MUST take less time to calculate
	//	than the timeout set in dualminer_open()
	//	This one takes ~0.53ms on Rev3 Icarus
	const char golden_ob[] =
		"4679ba4ec99876bf4bfe086082b40025"
		"4df6c356451471139a3afa71e48f544a"
		"00000000000000000000000000000000"
		"0000000087320b1a1426674f2fa722ce";

	const char golden_nonce[] = "000187a2";
	const uint32_t golden_nonce_val = 0x000187a2;
	unsigned char nonce_bin[DUALMINER_READ_SIZE];
	struct DUALMINER_WORK workdata;
	char *nonce_hex;
	int baud, uninitialised_var(work_division), uninitialised_var(fpga_count);
	struct cgpu_info *dualminer;
	int ret, err, amount, tries, i;
	bool ok;
	bool cmr2_ok[CAIRNSMORE2_INTS];
	bool anu_freqset = false;
	int cmr2_count;

	if ((sizeof(workdata) << 1) != (sizeof(golden_ob) - 1))
		quithere(1, "Data and golden_ob sizes don't match");

	dualminer = usb_alloc_cgpu(&dualminer_drv, 1);

	if (!usb_init(dualminer, dev, found))
		goto shin;

	get_options(this_option_offset, dualminer, &baud, &work_division, &fpga_count);

	hex2bin((void *)(&workdata), golden_ob, sizeof(workdata));

	info = (struct DUALMINER_INFO *)calloc(1, sizeof(struct DUALMINER_INFO));
	if (unlikely(!info))
		quit(1, "Failed to malloc DUALMINER_INFO");
	dualminer->device_data = (void *)info;

	info->ident = usb_ident(dualminer);
	switch (info->ident) {
		case IDENT_DM:
		break;
		default:
			quit(1, "%s dualminer_detect_one() invalid %s ident=%d",
				dualminer->drv->dname, dualminer->drv->dname, info->ident);
	}

	info->nonce_size = DUALMINER_READ_SIZE;
// For CMR2 test each USB Interface

cmr2_retry:

	tries = 2;
	ok = false;
	while (!ok && tries-- > 0) {
		dualminer_initialise(dualminer, baud);

		if (info->ident == IDENT_ANU && !set_anu_freq(dualminer, info)) {
			applog(LOG_WARNING, "%s %i: Failed to set frequency, too much overclock?",
			       dualminer->drv->name, dualminer->device_id);
			continue;
		}

		err = usb_write_ii(dualminer, info->intinfo,
				   (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);

		if (err != LIBUSB_SUCCESS || amount != sizeof(workdata))
			continue;

		memset(nonce_bin, 0, sizeof(nonce_bin));
		ret = dualminer_get_nonce(dualminer, nonce_bin, &tv_start, &tv_finish, NULL, 100);
		if (ret != ICA_NONCE_OK)
			continue;

		if (info->nonce_size == DUALMINER_READ_SIZE && usb_buffer_size(dualminer) == 1) {
			usb_buffer_clear(dualminer);
			dualminer->usbdev->ident = info->ident = IDENT_ANU;
			info->nonce_size = ANT_READ_SIZE;
			info->Hs = ANTMINERUSB_HASH_TIME;
			dualminer->drv->name = "ANU";
			applog(LOG_DEBUG, "%s %i: Detected Antminer U1, changing nonce size to %d",
			       dualminer->drv->name, dualminer->device_id, ANT_READ_SIZE);
		}

		nonce_hex = bin2hex(nonce_bin, sizeof(nonce_bin));
		if (strncmp(nonce_hex, golden_nonce, 8) == 0) {
			if (info->ident == IDENT_ANU && !anu_freqset)
				anu_freqset = true;
			else
				ok = true;
		} else {
			if (tries < 0 && info->ident != IDENT_CMR2) {
				applog(LOG_ERR,
					"Icarus Detect: "
					"Test failed at %s: get %s, should: %s",
					dualminer->device_path, nonce_hex, golden_nonce);
			}
		}
		free(nonce_hex);
	}

	if (!ok) {
		if (info->ident != IDENT_CMR2)
			goto unshin;

		if (info->intinfo < CAIRNSMORE2_INTS-1) {
			info->intinfo++;
			goto cmr2_retry;
		}
	} else {
		if (info->ident == IDENT_CMR2) {
			applog(LOG_DEBUG,
				"Icarus Detect: "
				"Test succeeded at %s i%d: got %s",
					dualminer->device_path, info->intinfo, golden_nonce);

			cmr2_ok[info->intinfo] = true;
			cmr2_count++;
			if (info->intinfo < CAIRNSMORE2_INTS-1) {
				info->intinfo++;
				goto cmr2_retry;
			}
		}
	}

	if (info->ident == IDENT_CMR2) {
		if (cmr2_count == 0) {
			applog(LOG_ERR,
				"Icarus Detect: Test failed at %s: for all %d CMR2 Interfaces",
				dualminer->device_path, CAIRNSMORE2_INTS);
			goto unshin;
		}

		// set the interface to the first one that succeeded
		for (i = 0; i < CAIRNSMORE2_INTS; i++)
			if (cmr2_ok[i]) {
				info->intinfo = i;
				break;
			}
	} else {
		applog(LOG_DEBUG,
			"Icarus Detect: "
			"Test succeeded at %s: got %s",
				dualminer->device_path, golden_nonce);
	}

	/* We have a real Icarus! */
	if (!add_cgpu(dualminer))
		goto unshin;

	update_usb_stats(dualminer);

	applog(LOG_INFO, "%s%d: Found at %s",
		dualminer->drv->name, dualminer->device_id, dualminer->device_path);

	if (info->ident == IDENT_CMR2) {
		applog(LOG_INFO, "%s%d: with %d Interface%s",
				dualminer->drv->name, dualminer->device_id,
				cmr2_count, cmr2_count > 1 ? "s" : "");

		// Assume 1 or 2 are running FPGA pairs
		if (cmr2_count < 3) {
			work_division = fpga_count = 2;
			info->Hs /= 2;
		}
	}

	applog(LOG_DEBUG, "%s%d: Init baud=%d work_division=%d fpga_count=%d",
		dualminer->drv->name, dualminer->device_id, baud, work_division, fpga_count);

	info->baud = baud;
	info->work_division = work_division;
	info->fpga_count = fpga_count;
	info->nonce_mask = mask(work_division);

	info->golden_hashes = (golden_nonce_val & info->nonce_mask) * fpga_count;
	timersub(&tv_finish, &tv_start, &(info->golden_tv));

	set_timing_mode(this_option_offset, dualminer);
	
	if (info->ident == IDENT_CMR2) {
		int i;
		for (i = info->intinfo + 1; i < dualminer->usbdev->found->intinfo_count; i++) {
			struct cgpu_info *cgtmp;
			struct DUALMINER_INFO *intmp;

			if (!cmr2_ok[i])
				continue;

			cgtmp = usb_copy_cgpu(dualminer);
			if (!cgtmp) {
				applog(LOG_ERR, "%s%d: Init failed initinfo %d",
						dualminer->drv->name, dualminer->device_id, i);
				continue;
			}

			cgtmp->usbinfo.usbstat = USB_NOSTAT;

			intmp = (struct DUALMINER_INFO *)malloc(sizeof(struct DUALMINER_INFO));
			if (unlikely(!intmp))
				quit(1, "Failed2 to malloc DUALMINER_INFO");

			cgtmp->device_data = (void *)intmp;

			// Initialise everything to match
			memcpy(intmp, info, sizeof(struct DUALMINER_INFO));

			intmp->intinfo = i;

			dualminer_initialise(cgtmp, baud);

			if (!add_cgpu(cgtmp)) {
				usb_uninit(cgtmp);
				free(intmp);
				continue;
			}

			update_usb_stats(cgtmp);
		}
	}

	return dualminer;

unshin:

	usb_uninit(dualminer);
	free(info);
	dualminer->device_data = NULL;

shin:

	dualminer = usb_free_cgpu(dualminer);

	return NULL;
}

static void dualminer_detect(bool __maybe_unused hotplug)
{
	usb_detect(&dualminer_drv, dualminer_detect_one);
}

static bool dualminer_prepare(__maybe_unused struct thr_info *thr)
{
//	struct cgpu_info *dualminer = thr->cgpu;

	return true;
}

static void cmr2_command(struct cgpu_info *dualminer, uint8_t cmd, uint8_t data)
{
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(dualminer->device_data);
	struct DUALMINER_WORK workdata;
	int amount;

	memset((void *)(&workdata), 0, sizeof(workdata));

	workdata.prefix = DUALMINER_CMR2_PREFIX;
	workdata.cmd = cmd;
	workdata.data = data;
	workdata.check = workdata.data ^ workdata.cmd ^ workdata.prefix ^ DUALMINER_CMR2_CHECK;

	usb_write_ii(dualminer, info->intinfo, (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);
}

static void cmr2_commands(struct cgpu_info *dualminer)
{
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(dualminer->device_data);

	if (info->speed_next_work) {
		info->speed_next_work = false;
		cmr2_command(dualminer, DUALMINER_CMR2_CMD_SPEED, info->cmr2_speed);
		return;
	}

	if (info->flash_next_work) {
		info->flash_next_work = false;
		cmr2_command(dualminer, DUALMINER_CMR2_CMD_FLASH, DUALMINER_CMR2_DATA_FLASH_ON);
		cgsleep_ms(250);
		cmr2_command(dualminer, DUALMINER_CMR2_CMD_FLASH, DUALMINER_CMR2_DATA_FLASH_OFF);
		cgsleep_ms(250);
		cmr2_command(dualminer, DUALMINER_CMR2_CMD_FLASH, DUALMINER_CMR2_DATA_FLASH_ON);
		cgsleep_ms(250);
		cmr2_command(dualminer, DUALMINER_CMR2_CMD_FLASH, DUALMINER_CMR2_DATA_FLASH_OFF);
		return;
	}
}

static int64_t dualminer_scanwork(struct thr_info *thr)
{
	struct cgpu_info *dualminer = thr->cgpu;
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(dualminer->device_data);
	int ret, err, amount;
	unsigned char nonce_bin[DUALMINER_BUF_SIZE];
	struct DUALMINER_WORK workdata;
	char *ob_hex;
	uint32_t nonce;
	int64_t hash_count = 0;
	struct timeval tv_start, tv_finish, elapsed;
	struct timeval tv_history_start, tv_history_finish;
	double Ti, Xi;
	int curr_hw_errors, i;
	bool was_hw_error;
	struct work *work;

	struct DUALMINER_HISTORY *history0, *history;
	int count;
	double Hs, W, fullnonce;
	int read_time;
	bool limited;
	int64_t estimate_hashes;
	uint32_t values;
	int64_t hash_count_range;

	if (unlikely(share_work_tdiff(dualminer) > info->fail_time)) {
		if (info->failing) {
			if (share_work_tdiff(dualminer) > info->fail_time + 60) {
				applog(LOG_ERR, "%s %d: Device failed to respond to restart",
				       dualminer->drv->name, dualminer->device_id);
				usb_nodev(dualminer);
				return -1;
			}
		} else {
			applog(LOG_WARNING, "%s %d: No valid hashes for over %d secs, attempting to reset",
			       dualminer->drv->name, dualminer->device_id, info->fail_time);
			usb_reset(dualminer);
			info->failing = true;
		}
	}

	// Device is gone
	if (dualminer->usbinfo.nodev)
		return -1;

	elapsed.tv_sec = elapsed.tv_usec = 0;

	work = get_work(thr, thr->id);
	memset((void *)(&workdata), 0, sizeof(workdata));
	memcpy(&(workdata.midstate), work->midstate, DUALMINER_MIDSTATE_SIZE);
	memcpy(&(workdata.work), work->data + DUALMINER_WORK_DATA_OFFSET, DUALMINER_WORK_SIZE);
	rev((void *)(&(workdata.midstate)), DUALMINER_MIDSTATE_SIZE);
	rev((void *)(&(workdata.work)), DUALMINER_WORK_SIZE);

	if (info->speed_next_work || info->flash_next_work)
		cmr2_commands(dualminer);

	// We only want results for the work we are about to send
	usb_buffer_clear(dualminer);

	err = usb_write_ii(dualminer, info->intinfo, (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);
	if (err < 0 || amount != sizeof(workdata)) {
		applog(LOG_ERR, "%s%i: Comms error (werr=%d amt=%d)",
				dualminer->drv->name, dualminer->device_id, err, amount);
		dev_error(dualminer, REASON_DEV_COMMS_ERROR);
		dualminer_initialise(dualminer, info->baud);
		goto out;
	}

	if (opt_debug) {
		ob_hex = bin2hex((void *)(&workdata), sizeof(workdata));
		applog(LOG_DEBUG, "%s%d: sent %s",
			dualminer->drv->name, dualminer->device_id, ob_hex);
		free(ob_hex);
	}

	/* Icarus will return 4 bytes (DUALMINER_READ_SIZE) nonces or nothing */
	memset(nonce_bin, 0, sizeof(nonce_bin));
	ret = dualminer_get_nonce(dualminer, nonce_bin, &tv_start, &tv_finish, thr, info->read_time);
	if (ret == ICA_NONCE_ERROR)
		goto out;

	// aborted before becoming idle, get new work
	if (ret == ICA_NONCE_TIMEOUT || ret == ICA_NONCE_RESTART) {
		timersub(&tv_finish, &tv_start, &elapsed);

		// ONLY up to just when it aborted
		// We didn't read a reply so we don't subtract DUALMINER_READ_TIME
		estimate_hashes = ((double)(elapsed.tv_sec)
					+ ((double)(elapsed.tv_usec))/((double)1000000)) / info->Hs;

		// If some Serial-USB delay allowed the full nonce range to
		// complete it can't have done more than a full nonce
		if (unlikely(estimate_hashes > 0xffffffff))
			estimate_hashes = 0xffffffff;

		applog(LOG_DEBUG, "%s%d: no nonce = 0x%08lX hashes (%ld.%06lds)",
				dualminer->drv->name, dualminer->device_id,
				(long unsigned int)estimate_hashes,
				(long)elapsed.tv_sec, (long)elapsed.tv_usec);

		hash_count = estimate_hashes;
		goto out;
	}

	memcpy((char *)&nonce, nonce_bin, DUALMINER_READ_SIZE);
	nonce = htobe32(nonce);
	curr_hw_errors = dualminer->hw_errors;
	if (submit_nonce(thr, work, nonce))
		info->failing = false;
	was_hw_error = (curr_hw_errors < dualminer->hw_errors);

	if (was_hw_error)
		hash_count = 0;
	else {
		hash_count = (nonce & info->nonce_mask);
		hash_count++;
		hash_count *= info->fpga_count;
	}

#if 0
	// This appears to only return zero nonce values
	if (usb_buffer_size(dualminer) > 3) {
		memcpy((char *)&nonce, dualminer->usbdev->buffer, sizeof(nonce_bin));
		nonce = htobe32(nonce);
		applog(LOG_WARNING, "%s%d: attempting to submit 2nd nonce = 0x%08lX",
				dualminer->drv->name, dualminer->device_id,
				(long unsigned int)nonce);
		curr_hw_errors = dualminer->hw_errors;
		submit_nonce(thr, work, nonce);
		was_hw_error = (curr_hw_errors > dualminer->hw_errors);
	}
#endif

	if (opt_debug || info->do_dualminer_timing)
		timersub(&tv_finish, &tv_start, &elapsed);

	applog(LOG_DEBUG, "%s%d: nonce = 0x%08x = 0x%08lX hashes (%ld.%06lds)",
			dualminer->drv->name, dualminer->device_id,
			nonce, (long unsigned int)hash_count,
			(long)elapsed.tv_sec, (long)elapsed.tv_usec);

	// Ignore possible end condition values ... and hw errors
	// TODO: set limitations on calculated values depending on the device
	// to avoid crap values caused by CPU/Task Switching/Swapping/etc
	if (info->do_dualminer_timing
	&&  !was_hw_error
	&&  ((nonce & info->nonce_mask) > END_CONDITION)
	&&  ((nonce & info->nonce_mask) < (info->nonce_mask & ~END_CONDITION))) {
		cgtime(&tv_history_start);

		history0 = &(info->history[0]);

		if (history0->values == 0)
			timeradd(&tv_start, &history_sec, &(history0->finish));

		Ti = (double)(elapsed.tv_sec)
			+ ((double)(elapsed.tv_usec))/((double)1000000)
			- ((double)DUALMINER_READ_TIME(info->baud));
		Xi = (double)hash_count;
		history0->sumXiTi += Xi * Ti;
		history0->sumXi += Xi;
		history0->sumTi += Ti;
		history0->sumXi2 += Xi * Xi;

		history0->values++;

		if (history0->hash_count_max < hash_count)
			history0->hash_count_max = hash_count;
		if (history0->hash_count_min > hash_count || history0->hash_count_min == 0)
			history0->hash_count_min = hash_count;

		if (history0->values >= info->min_data_count
		&&  timercmp(&tv_start, &(history0->finish), >)) {
			for (i = INFO_HISTORY; i > 0; i--)
				memcpy(&(info->history[i]),
					&(info->history[i-1]),
					sizeof(struct DUALMINER_HISTORY));

			// Initialise history0 to zero for summary calculation
			memset(history0, 0, sizeof(struct DUALMINER_HISTORY));

			// We just completed a history data set
			// So now recalc read_time based on the whole history thus we will
			// initially get more accurate until it completes INFO_HISTORY
			// total data sets
			count = 0;
			for (i = 1 ; i <= INFO_HISTORY; i++) {
				history = &(info->history[i]);
				if (history->values >= MIN_DATA_COUNT) {
					count++;

					history0->sumXiTi += history->sumXiTi;
					history0->sumXi += history->sumXi;
					history0->sumTi += history->sumTi;
					history0->sumXi2 += history->sumXi2;
					history0->values += history->values;

					if (history0->hash_count_max < history->hash_count_max)
						history0->hash_count_max = history->hash_count_max;
					if (history0->hash_count_min > history->hash_count_min || history0->hash_count_min == 0)
						history0->hash_count_min = history->hash_count_min;
				}
			}

			// All history data
			Hs = (history0->values*history0->sumXiTi - history0->sumXi*history0->sumTi)
				/ (history0->values*history0->sumXi2 - history0->sumXi*history0->sumXi);
			W = history0->sumTi/history0->values - Hs*history0->sumXi/history0->values;
			hash_count_range = history0->hash_count_max - history0->hash_count_min;
			values = history0->values;
			
			// Initialise history0 to zero for next data set
			memset(history0, 0, sizeof(struct DUALMINER_HISTORY));

			fullnonce = W + Hs * (((double)0xffffffff) + 1);
			read_time = SECTOMS(fullnonce) - DUALMINER_READ_REDUCE;
			if (info->read_time_limit > 0 && read_time > info->read_time_limit) {
				read_time = info->read_time_limit;
				limited = true;
			} else
				limited = false;

			info->Hs = Hs;
			info->read_time = read_time;

			info->fullnonce = fullnonce;
			info->count = count;
			info->W = W;
			info->values = values;
			info->hash_count_range = hash_count_range;

			if (info->min_data_count < MAX_MIN_DATA_COUNT)
				info->min_data_count *= 2;
			else if (info->timing_mode == MODE_SHORT)
				info->do_dualminer_timing = false;

			applog(LOG_WARNING, "%s%d Re-estimate: Hs=%e W=%e read_time=%dms%s fullnonce=%.3fs",
					dualminer->drv->name, dualminer->device_id, Hs, W, read_time,
					limited ? " (limited)" : "", fullnonce);
		}
		info->history_count++;
		cgtime(&tv_history_finish);

		timersub(&tv_history_finish, &tv_history_start, &tv_history_finish);
		timeradd(&tv_history_finish, &(info->history_time), &(info->history_time));
	}
out:
	free_work(work);

	return hash_count;
}

static struct api_data *dualminer_api_stats(struct cgpu_info *cgpu)
{
	struct api_data *root = NULL;
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(cgpu->device_data);

	// Warning, access to these is not locked - but we don't really
	// care since hashing performance is way more important than
	// locking access to displaying API debug 'stats'
	// If locking becomes an issue for any of them, use copy_data=true also
	root = api_add_int(root, "read_time", &(info->read_time), false);
	root = api_add_int(root, "read_time_limit", &(info->read_time_limit), false);
	root = api_add_double(root, "fullnonce", &(info->fullnonce), false);
	root = api_add_int(root, "count", &(info->count), false);
	root = api_add_hs(root, "Hs", &(info->Hs), false);
	root = api_add_double(root, "W", &(info->W), false);
	root = api_add_uint(root, "total_values", &(info->values), false);
	root = api_add_uint64(root, "range", &(info->hash_count_range), false);
	root = api_add_uint64(root, "history_count", &(info->history_count), false);
	root = api_add_timeval(root, "history_time", &(info->history_time), false);
	root = api_add_uint(root, "min_data_count", &(info->min_data_count), false);
	root = api_add_uint(root, "timing_values", &(info->history[0].values), false);
	root = api_add_const(root, "timing_mode", timing_mode_str(info->timing_mode), false);
	root = api_add_bool(root, "is_timing", &(info->do_dualminer_timing), false);
	root = api_add_int(root, "baud", &(info->baud), false);
	root = api_add_int(root, "work_division", &(info->work_division), false);
	root = api_add_int(root, "fpga_count", &(info->fpga_count), false);

	return root;
}

static void dualminer_statline_before(char *buf, size_t bufsiz, struct cgpu_info *cgpu)
{
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(cgpu->device_data);

	if (info->ident == IDENT_CMR2 && info->cmr2_speed > 0)
		tailsprintf(buf, bufsiz, "%5.1fMhz", (float)(info->cmr2_speed) * DUALMINER_CMR2_SPEED_FACTOR);
}

static void dualminer_shutdown(__maybe_unused struct thr_info *thr)
{
	// TODO: ?
}

static void dualminer_identify(struct cgpu_info *cgpu)
{
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(cgpu->device_data);

	if (info->ident == IDENT_CMR2)
		info->flash_next_work = true;
}

static char *dualminer_set(struct cgpu_info *cgpu, char *option, char *setting, char *replybuf)
{
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(cgpu->device_data);
	int val;

	if (info->ident != IDENT_CMR2) {
		strcpy(replybuf, "no set options available");
		return replybuf;
	}

	if (strcasecmp(option, "help") == 0) {
		sprintf(replybuf, "clock: range %d-%d",
				  DUALMINER_CMR2_SPEED_MIN_INT, DUALMINER_CMR2_SPEED_MAX_INT);
		return replybuf;
	}

	if (strcasecmp(option, "clock") == 0) {
		if (!setting || !*setting) {
			sprintf(replybuf, "missing clock setting");
			return replybuf;
		}

		val = atoi(setting);
		if (val < DUALMINER_CMR2_SPEED_MIN_INT || val > DUALMINER_CMR2_SPEED_MAX_INT) {
			sprintf(replybuf, "invalid clock: '%s' valid range %d-%d",
					  setting,
					  DUALMINER_CMR2_SPEED_MIN_INT,
					  DUALMINER_CMR2_SPEED_MAX_INT);
		}

		info->cmr2_speed = CMR2_INT_TO_SPEED(val);
		info->speed_next_work = true;

		return NULL;
	}

	sprintf(replybuf, "Unknown option: %s", option);
	return replybuf;
}

struct device_drv dualminer_drv = {
	.drv_id = DRIVER_dualminer,
	.dname = "Dualminer",
	.name = "DM",
	.drv_detect = dualminer_detect,
	.hash_work = &hash_driver_work,
	.get_api_stats = dualminer_api_stats,
	.get_statline_before = dualminer_statline_before,
	.set_device = dualminer_set,
	.identify_device = dualminer_identify,
	.thread_prepare = dualminer_prepare,
	.scanwork = dualminer_scanwork,
	.thread_shutdown = dualminer_shutdown,
};
