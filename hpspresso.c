/*-
 * Copyright (c) 2015-2022 Hans Petter Selasky
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */
#define	_WITH_GETLINE
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/queue.h>
#include <err.h>
#include <math.h>
#include <sysexits.h>

#include <math_bin.h>

struct try_solve_args {
	uint32_t bitno;
	uint32_t lorder;
	uint32_t mincount;
	uint32_t *map;
	uint32_t *min;
};

static uint32_t input_bits;
static uint32_t input_bits_sd;
static uint32_t output_bits;
static FILE *fp;
static uint8_t do_verify;
static uint8_t do_compress;
static uint8_t do_xor;
static uint8_t do_float;
static uint8_t do_full_range;
static uint8_t do_slow;
static uint8_t do_or;
static int do_subdivide;
static uint8_t do_sumbits;
static uint32_t do_skip;
static uint32_t do_mod;

typedef TAILQ_HEAD(, table_entry) phead_t;

static phead_t head;
static phead_t rhead;

struct table_entry {
	TAILQ_ENTRY(table_entry) entry;
	uint16_t *input_value;
	uint16_t *input_mask;
	uint16_t *output_value;
	uint16_t *output_mask;
	double	output_d64;
};

static uint8_t output_bit_get(struct table_entry *, uint32_t);
static void output_bit_clr(struct table_entry *, uint32_t);
static void output_bit_set(struct table_entry *, uint32_t);

static double
mod(double input)
{
	long long value = input;

	input -= value;

	value %= (long long)do_mod;
	if (value < 0)
		value += do_mod;
	return (input + value);
}

static struct table_entry *
alloc_new_table_entry_u32(struct table_entry *src, uint32_t bitno)
{
	struct table_entry *ptr;
	uint32_t istride = (input_bits + 15) / 16;
	uint32_t ostride = (output_bits + 15) / 16;
	size_t size = sizeof(*ptr) + (4 * istride) + (4 * ostride);

	ptr = malloc(size);
	if (ptr == NULL)
		errx(1, "Out of memory");
	if (src == NULL)
		memset(ptr, 0, size);

	ptr->input_value = (uint16_t *)(ptr + 1);
	ptr->input_mask = ptr->input_value + istride;
	ptr->output_value = ptr->input_mask + istride;
	ptr->output_mask = ptr->output_value + ostride;

	if (src != NULL) {
		/* copy full value */
		memcpy(ptr->input_value, src->input_value, istride * 2);
		memcpy(ptr->input_mask, src->input_mask, istride * 2);

		if (bitno == -1U) {
			/* copy full value */
			memcpy(ptr->output_value, src->output_value, ostride * 2);
			memcpy(ptr->output_mask, src->output_mask, ostride * 2);
		} else {
			uint16_t m = (1 << (bitno % 16));
			uint32_t x = (bitno / 16);

			/* set zero default */
			memset(ptr->output_value, 0, ostride * 2);
			memset(ptr->output_mask, 0, ostride * 2);
			/* copy only one bit */
			ptr->output_value[x] = src->output_value[x] & m;
			ptr->output_mask[x] = src->output_mask[x] & m;
		}
	}
	return (ptr);
}

static struct table_entry *
alloc_new_table_entry_d64(struct table_entry *src, uint32_t bitno)
{
	struct table_entry *ptr;
	uint32_t istride = (input_bits + 15) / 16;
	size_t size = sizeof(*ptr) + (4 * istride);

	ptr = malloc(size);
	if (ptr == NULL)
		errx(1, "Out of memory");
	if (src == NULL)
		memset(ptr, 0, size);

	ptr->input_value = (uint16_t *)(ptr + 1);
	ptr->input_mask = ptr->input_value + istride;

	if (src != NULL) {
		/* copy full value */
		memcpy(ptr->input_value, src->input_value, istride * 2);
		memcpy(ptr->input_mask, src->input_mask, istride * 2);
		ptr->output_d64 = src->output_d64;
	}
	return (ptr);
}

static struct table_entry *
alloc_new_table_entry(struct table_entry *src, uint32_t bitno)
{
	if (do_float)
		return (alloc_new_table_entry_d64(src, bitno));
	else
		return (alloc_new_table_entry_u32(src, bitno));
}

static void
print_input_value(uint16_t *ptr)
{
	uint32_t x;

	for (x = 0; x != input_bits; x++) {
		if (ptr[x / 16] & (1 << (x % 16))) {
			printf("1");
		} else {
			printf("-");
		}
	}
}

static void
print_output_value(uint16_t *ptr)
{
	uint32_t x;

	for (x = 0; x != output_bits; x++) {
		if (ptr[x / 16] & (1 << (x % 16))) {
			printf("1");
		} else {
			printf("0");
		}
	}
}

static void
print_output(struct table_entry *entry)
{
	if (do_float == 2) {
		printf("%lld", (long long)entry->output_d64);
	} else if (do_float == 1) {
		printf("%f", entry->output_d64);
	} else {
		print_output_value(entry->output_value);
	}
}

static void
parse_header(void)
{
	char *line = NULL;
	size_t linecap = 0;
	ssize_t linelen;
	char ch = 0;

	while (input_bits == 0 || (ch == 0 && output_bits == 0) || (ch != 0 && ch != 'i' && ch != 'f')) {
		linelen = getline(&line, &linecap, fp);
		if (linelen <= 0)
			errx(1, "Invalid header, expected format is .i X or .o Y");
		if (sscanf(line, ".i %u\n", &input_bits) == 1)
			continue;
		if (sscanf(line, ".o %u\n", &output_bits) == 1)
			continue;
		if (sscanf(line, ".o %c\n", &ch) == 1)
			continue;
	}

	if (output_bits == 0 && ch == 'i') {
		do_float = 2;	/* integer mode */
		output_bits = 2;
	} else if (output_bits == 0 && ch == 'f') {
		do_float = 1;	/* floating point mode */
		output_bits = 2;
	} else if (output_bits == 0 && ch == 0) {
		errx(1, "Number of output bits is invalid");
	} else if (output_bits == 0 && ch != 0) {
		errx(1, "Output mode not supported: '%c'", ch);
	}

	if (do_subdivide > 1) {
		input_bits_sd = input_bits / do_subdivide;
		if (input_bits % do_subdivide)
			errx(1, "Number of input bits cannot be subdivided");
		printf("# Subdividing input into %dx%d bits\n",
		    input_bits_sd, do_subdivide);
	}
}

static uint8_t
increment(uint16_t *pv, uint16_t *pm)
{
	uint32_t x;

	for (x = 0; x != input_bits; x++) {
		uint16_t m = (1 << (x % 16));

		if (!(pm[x / 16] & m)) {
			pv[x / 16] ^= m;
			if (pv[x / 16] & m)
				return (0);
		}
	}
	return (1);
}

static void
parse_contents(void)
{
	struct table_entry *ptr = NULL;
	uint32_t offset = 0;
	double dp = 1.0;
	int ch;
	int comment = 0;
	bool sign = false;

	for (;;) {
		ch = fgetc(fp);

		if (comment) {
			if (ch >= 0 && ch != '\n')
				continue;
			comment = 0;
		}

		switch (ch) {
		case '9':
		case '8':
		case '7':
		case '6':
		case '5':
		case '4':
		case '3':
		case '2':
			if (do_float == 0 || offset < input_bits) {
				if (ptr == NULL)
					ptr = alloc_new_table_entry(NULL, 0);
				offset++;
				break;
			}
			/* FALLTHROUGH */
		case '1':
			if (ptr == NULL)
				ptr = alloc_new_table_entry(NULL, 0);
			if (offset < input_bits) {
				uint16_t m = 1 << (offset % 16);

				ptr->input_value[offset / 16] |= m;
				ptr->input_mask[offset / 16] |= m;
				offset++;
			} else if (do_float == 0) {
				uint16_t m = 1 << ((offset - input_bits) % 16);

				ptr->output_value[(offset - input_bits) / 16] |= m;
				ptr->output_mask[(offset - input_bits) / 16] |= m;
				offset++;
			} else {
				if (dp == 1.0) {
					ptr->output_d64 *= 10.0;
					ptr->output_d64 += ch - '0';
				} else {
					ptr->output_d64 += (ch - '0') * dp;
					dp /= 10.0;
				}
				if (offset == input_bits)
					offset++;
			}
			break;
		case '0':
			if (ptr == NULL)
				ptr = alloc_new_table_entry(NULL, 0);
			if (offset < input_bits) {
				uint16_t m = 1 << (offset % 16);

				ptr->input_mask[offset / 16] |= m;
				offset++;
			} else if (do_float == 0) {
				uint16_t m = 1 << ((offset - input_bits) % 16);

				ptr->output_mask[(offset - input_bits) / 16] |= m;
				offset++;
			} else {
				if (dp == 1.0)
					ptr->output_d64 *= 10.0;
				else
					dp /= 10.0;
				if (offset == input_bits)
					offset++;
			}
			break;
		case '-':
			if (do_float != 0 && offset >= input_bits) {
				if (ptr == NULL)
					ptr = alloc_new_table_entry(NULL, 0);
				if (sign)
					errx(1, "Double sign in front of value");
				sign = !sign;

				if (offset == input_bits)
					offset++;
				break;
			}
		case '~':
			if (do_float == 0 || offset < input_bits) {
				if (ptr == NULL)
					ptr = alloc_new_table_entry(NULL, 0);
				offset++;
			}
			if (do_float != 0 && offset > input_bits)
				offset++;
			break;
		case '.':
			if (do_float != 0 && offset >= input_bits) {
				if (dp != 1.0)
					errx(1, "Error parsing floating point value, double '.' character");
				dp /= 10.0;

				if (offset == input_bits)
					offset++;
				break;
			}
			if (offset != 0)
				break;
		case '#':
			if (do_float != 0 && offset > input_bits)
				offset++;
			comment = 1;
			break;
		default:
			if (do_float != 0 && offset > input_bits)
				offset++;
			break;
		}
		if (offset == (input_bits + output_bits)) {
			if (do_float != 0 && sign != 0)
				ptr->output_d64 = -ptr->output_d64;
#if 0
			printf("in=%d out=%d\n", input_bits, output_bits);
			print_input_value(ptr->input_value);
			printf(" IV\n");
			print_input_value(ptr->input_mask);
			printf(" IM\n");
			print_output(ptr); printf("\n");
#endif
			do {
				struct table_entry *pnew;

				pnew = alloc_new_table_entry(ptr, -1U);
				memset(pnew->input_mask, 255, 2 * ((input_bits + 15) / 16));
				TAILQ_INSERT_TAIL(&head, pnew, entry);
			} while (!increment(ptr->input_value, ptr->input_mask));

			free(ptr);
			ptr = NULL;
			offset = 0;
			sign = 0;
			dp = 1.0;
		}
		if (ch < 0)
			break;
	}
	if (ptr != NULL)
		errx(1, "Incomplete line at end of file!");
}

/*
 * Main solver component
 */
static void
generate_bitmap(uint16_t *ptr, uint16_t **ppout, uint32_t start, uint32_t max, uint32_t level)
{
	uint32_t x;

	if (level == 0) {
		uint32_t istride = (input_bits + 15) / 16;

		memcpy(*ppout, ptr, 2 * istride);
		*ppout += istride;
		return;
	}
	for (x = start; x != max; x++) {
		ptr[x / 16] |= (1 << (x % 16));
		generate_bitmap(ptr, ppout, x + 1, max, level - 1);
		ptr[x / 16] &= ~(1 << (x % 16));
	}
}

static void
generate_subdivided(uint16_t **ppout, uint32_t istride)
{
	uint16_t *ptr = *ppout;
	uint32_t vx;
	uint32_t vy;
	uint32_t ox;
	uint32_t oy;
	uint8_t sa;
	uint8_t sb;

	for (sa = 0; sa != do_subdivide; sa++) {
		for (sb = sa + 1; sb != do_subdivide; sb++) {
			/* give prio to AND */
			for (vx = 0; vx != input_bits_sd; vx++) {
				ox = vx + sa * input_bits_sd;
				oy = vx + sb * input_bits_sd;
				memset(ptr, 0, 2 * istride);
				ptr[ox / 16] |= (1 << (ox % 16));
				ptr[oy / 16] |= (1 << (oy % 16));
				ptr += istride;
			}
			for (vx = 0; vx != input_bits_sd; vx++) {
				ox = vx + sa * input_bits_sd;
				for (vy = 0; vy != input_bits_sd; vy++) {
					if (vx == vy)
						continue;
					oy = vy + sb * input_bits_sd;
					memset(ptr, 0, 2 * istride);
					ptr[ox / 16] |= (1 << (ox % 16));
					ptr[oy / 16] |= (1 << (oy % 16));
					ptr += istride;
				}
			}
		}
	}
	*ppout = ptr;
}

static int8_t
func(uint16_t *pa, uint16_t *pb, uint16_t *pm)
{
	size_t istride = (input_bits + 15) / 16;

	if (pm != NULL) {
		if (do_sumbits) {
			int8_t bits = 0;

			while (istride--)
				bits += mbin_sumbits16(pa[istride] & pb[istride] & pm[istride]);
			return ((bits & 1) ? -1 : 1);
		} else if (do_or) {
			while (istride--) {
				uint16_t b = (pm[istride] & pb[istride]);

				if ((pa[istride] | b) != b)
					return (0);
			}
		} else {
			while (istride--) {
				if ((pa[istride] & pm[istride]) != pb[istride])
					return (0);
			}
		}
	} else {
		if (do_sumbits) {
			int8_t bits = 0;

			while (istride--)
				bits += mbin_sumbits16(pa[istride] & pb[istride]);
			return ((bits & 1) ? -1 : 1);
		} else if (do_or) {
			while (istride--) {
				if ((pa[istride] | pb[istride]) != pb[istride])
					return (0);
			}
		} else {
			while (istride--) {
				if ((pa[istride] & pb[istride]) != pb[istride])
					return (0);
			}
		}
	}
	return (1);
}

static uint8_t
try_solve_sub_32(uint32_t *map, uint32_t *pcount, uint32_t lorder, uint32_t bitno)
{
	struct table_entry *entry;
	struct table_entry *rentry;
	struct mbin_eq_32 *ptr;
	struct mbin_eq_32 *tmp;
	mbin_eq_head_32_t phead;
	uint32_t istride = (input_bits + 15) / 16;
	uint16_t *bitmap;
	uint16_t *bitmap_ptr;
	uint16_t scratch[istride];
	uint32_t *array;
	uint32_t total;
	uint32_t x;
	uint32_t y;
	uint32_t z;

	TAILQ_INIT(&phead);

	if (lorder > input_bits)
		lorder = input_bits;

	/* allocate offset array */
	x = (input_bits + 1) * sizeof(array[0]);
	array = malloc(x);
	memset(array, 255, x);

	/* compute number of bits needed */
	for (total = y = 0; y <= lorder; y++) {
		if (map == 0)
			x = y;
		else
			x = map[y];
		if (array[x] == -1U) {
			array[x] = total;
			if (x < do_skip)
				continue;
			if (do_subdivide > 1 && x == 2) {
				total += input_bits_sd * input_bits_sd *
				    mbin_coeff_32(do_subdivide, 2);
			} else {
				total += mbin_coeff_32(input_bits, x);
			}
		}
	}
	bitmap = malloc(total * 2 * istride);

	memset(scratch, 0, sizeof(scratch));

	/* build variable map */
	for (x = 0; x <= input_bits; x++) {
		if (array[x] == -1U)
			continue;
		bitmap_ptr = bitmap + (array[x] * istride);
		if (x < do_skip)
			continue;
		if (do_subdivide > 1 && x == 2) {
			generate_subdivided(&bitmap_ptr, istride);
		} else {
			generate_bitmap(scratch, &bitmap_ptr, 0, input_bits, x);
		}
	}

	/* build equation */
	TAILQ_FOREACH(entry, &head, entry) {
		uint16_t m = (1 << (bitno % 16));

		if (!(entry->output_mask[bitno / 16] & m))
			continue;
		do {
			ptr = mbin_eq_alloc_32(total);
			for (y = 0; y != total; y++) {
				if (func(entry->input_value, &bitmap[y * istride], NULL))
					MBIN_EQ_BIT_SET(ptr->bitdata, y);
			}
			ptr->value = (entry->output_value[bitno / 16] & m) ? 1 : 0;
			TAILQ_INSERT_TAIL(&phead, ptr, entry);
		} while (!increment(entry->input_value, entry->input_mask));
	}

	/* solve equation */
	if (mbin_eq_solve_32(total, &phead)) {
		mbin_eq_free_head_32(&phead);
		free(bitmap);
		free(array);
		return (0);
	}
	if (pcount != 0) {
		(*pcount) = 0;
		TAILQ_FOREACH(ptr, &phead, entry) {
			if (ptr->value == 0)
				continue;
			(*pcount)++;
		}
		mbin_eq_free_head_32(&phead);
		free(bitmap);
		free(array);
		return (1);
	}
	TAILQ_FOREACH(ptr, &phead, entry) {
		if (ptr->value == 0)
			continue;
		for (x = 0; x < total; x += 16) {
			if (ptr->bitdata[x / 16] == 0)
				continue;
			for (; x != total; x++) {
				if (MBIN_EQ_BIT_GET(ptr->bitdata, x))
					break;
			}
			TAILQ_FOREACH(rentry, &rhead, entry) {
				if (memcmp(&bitmap[x * istride], rentry->input_value,
				    istride * 2) == 0)
					break;
			}
			if (rentry == NULL) {
				rentry = alloc_new_table_entry(NULL, 0);
				TAILQ_INSERT_TAIL(&rhead, rentry, entry);
				memcpy(rentry->input_value, &bitmap[x * istride],
				    istride * 2);
				memcpy(rentry->input_mask, &bitmap[x * istride],
				    istride * 2);
			}
			rentry->output_value[bitno / 16] |= (1 << (bitno % 16));
			break;
		}
	}
	mbin_eq_free_head_32(&phead);
	free(bitmap);
	free(array);
	return (1);
}

static void
try_solve_recursive_32(struct try_solve_args *args, uint32_t level)
{
	uint32_t count;
	uint32_t x;
	uint32_t y;

	for (y = 0; y != (input_bits + 1); y++) {
		for (x = 0; x != level; x++) {
			if (args->map[x] == y)
				break;
		}
		if (x != level)
			continue;

		args->map[level] = y;

		if (level == args->lorder) {
			if (try_solve_sub_32(args->map, &count, args->lorder, args->bitno)) {
				if (count < args->mincount) {
					printf("%d .. ", count);
					memcpy(args->min, args->map,
					    (args->lorder + 1) * sizeof(args->min[0]));
					args->mincount = count;
				}
			}
		} else {
			try_solve_recursive_32(args, level + 1);
			if (level >= do_slow)
				break;
		}
	}
}

static void
try_solve_32(uint32_t bitno)
{
	struct try_solve_args args;
	uint32_t x;

	args.bitno = bitno;
	args.map = alloca(sizeof(uint32_t) * (input_bits + 1));
	args.min = alloca(sizeof(uint32_t) * (input_bits + 1));

	/* setup default map */
	for (x = 0; x <= input_bits; x++) {
		args.map[x] = x;
		args.min[x] = x;
	}

	for (x = 0; x <= input_bits; x++) {
		if (try_solve_sub_32(args.map, &args.mincount, x, bitno))
			break;
	}
	args.lorder = x;
	if (x > input_bits) {
		printf("# Unsolvable\n");
		return;
	}
	printf("#  Solving O%d: %d .. ", x, args.mincount);
	if (do_slow != 0)
		try_solve_recursive_32(&args, 0);
	printf("\n");

	if (try_solve_sub_32(args.min, 0, args.lorder, args.bitno) == 0) {
		printf("# Unsolvable\n");
		return;
	}
}

static uint8_t
try_solve_sub_d64(uint32_t *map, uint32_t *pcount, uint32_t lorder)
{
	struct table_entry *entry;
	struct table_entry *rentry;
	struct mbin_eq_d64 *ptr;
	struct mbin_eq_d64 *tmp;
	mbin_eq_head_d64_t phead;
	uint32_t istride = (input_bits + 15) / 16;
	uint16_t *bitmap;
	uint16_t *bitmap_ptr;
	uint16_t scratch[istride];
	uint32_t *array;
	uint32_t total;
	uint32_t x;
	uint32_t y;
	uint32_t z;

	TAILQ_INIT(&phead);

	if (lorder > input_bits)
		lorder = input_bits;

	/* allocate offset array */
	x = (input_bits + 1) * sizeof(array[0]);
	array = malloc(x);
	memset(array, 255, x);

	/* compute number of bits needed */
	for (total = y = 0; y <= lorder; y++) {
		if (map == 0)
			x = y;
		else
			x = map[y];
		if (array[x] == -1U) {
			array[x] = total;
			if (x < do_skip)
				continue;
			if (do_subdivide > 1 && x == 2) {
				total += input_bits_sd * input_bits_sd *
				    mbin_coeff_32(do_subdivide, 2);
			} else {
				total += mbin_coeff_32(input_bits, x);
			}
		}
	}
	bitmap = malloc(total * 2 * istride);

	memset(scratch, 0, sizeof(scratch));

	/* build variable map */
	for (x = 0; x <= input_bits; x++) {
		if (array[x] == -1U)
			continue;
		bitmap_ptr = bitmap + (array[x] * istride);
		if (x < do_skip)
			continue;
		if (do_subdivide > 1 && x == 2) {
			generate_subdivided(&bitmap_ptr, istride);
		} else {
			generate_bitmap(scratch, &bitmap_ptr, 0, input_bits, x);
		}
	}

	/* build equation */
	TAILQ_FOREACH(entry, &head, entry) {
		do {
			ptr = mbin_eq_alloc_d64(total);
			for (y = 0; y != total; y++) {
				ptr->fdata[y] = func(entry->input_value, &bitmap[y * istride], NULL);
			}
			ptr->value = entry->output_d64;
			TAILQ_INSERT_TAIL(&phead, ptr, entry);
		} while (!increment(entry->input_value, entry->input_mask));
	}

	/* solve equation */
	if (mbin_eq_solve_d64(total, &phead, 1.0 / (1ULL << input_bits))) {
		mbin_eq_free_head_d64(&phead);
		free(bitmap);
		free(array);
		return (0);
	}
	if (do_mod != 0) {
		TAILQ_FOREACH(ptr, &phead, entry)
		    ptr->value = mod(ptr->value);
	}
	if (pcount != 0) {
		(*pcount) = 0;
		TAILQ_FOREACH(ptr, &phead, entry) {
			if (ptr->value == 0)
				continue;
			(*pcount)++;
		}
		mbin_eq_free_head_d64(&phead);
		free(bitmap);
		free(array);
		return (1);
	}
	TAILQ_FOREACH(ptr, &phead, entry) {
		if (ptr->value == 0.0)
			continue;
		for (x = 0; x < total; x++) {
			if (ptr->fdata[x] == 0.0)
				continue;
			TAILQ_FOREACH(rentry, &rhead, entry) {
				if (memcmp(&bitmap[x * istride], rentry->input_value,
				    istride * 2) == 0)
					break;
			}
			if (rentry == NULL) {
				rentry = alloc_new_table_entry(NULL, 0);
				TAILQ_INSERT_TAIL(&rhead, rentry, entry);
				memcpy(rentry->input_value, &bitmap[x * istride],
				    istride * 2);
				memcpy(rentry->input_mask, &bitmap[x * istride],
				    istride * 2);
			}
			rentry->output_d64 = ptr->value;
			break;
		}
	}
	mbin_eq_free_head_d64(&phead);
	free(bitmap);
	free(array);
	return (1);
}

static void
try_solve_recursive_d64(struct try_solve_args *args, uint32_t level)
{
	uint32_t count;
	uint32_t x;
	uint32_t y;

	for (y = 0; y != (input_bits + 1); y++) {
		for (x = 0; x != level; x++) {
			if (args->map[x] == y)
				break;
		}
		if (x != level)
			continue;

		args->map[level] = y;

		if (level == args->lorder) {
			if (try_solve_sub_d64(args->map, &count, args->lorder)) {
				if (count < args->mincount) {
					printf("%d .. ", count);
					memcpy(args->min, args->map,
					    (args->lorder + 1) * sizeof(args->min[0]));
					args->mincount = count;
				}
			}
		} else {
			try_solve_recursive_d64(args, level + 1);
			if (level >= do_slow)
				break;
		}
	}
}

static void
try_solve_d64(void)
{
	struct try_solve_args args;
	uint32_t x;

	args.bitno = -1U;
	args.map = alloca(sizeof(uint32_t) * (input_bits + 1));
	args.min = alloca(sizeof(uint32_t) * (input_bits + 1));

	/* setup default map */
	for (x = 0; x <= input_bits; x++) {
		args.map[x] = x;
		args.min[x] = x;
	}

	for (x = 0; x <= input_bits; x++) {
		if (try_solve_sub_d64(args.map, &args.mincount, x))
			break;
	}
	args.lorder = x;
	if (x > input_bits) {
		printf("# Unsolvable\n");
		return;
	}
	printf("#  Solving O%d: %d .. ", x, args.mincount);
	if (do_slow != 0)
		try_solve_recursive_d64(&args, 0);
	printf("\n");

	if (try_solve_sub_d64(args.min, 0, args.lorder) == 0) {
		printf("# Unsolvable\n");
		return;
	}
}

/*
 * Main compressor component
 */

static uint8_t
output_bit_get(struct table_entry *ptr, uint32_t bitno)
{
	return ((ptr->output_value[bitno / 16] & (1 << (bitno % 16))) ? 1 : 0);
}

static void
output_bit_clr(struct table_entry *ptr, uint32_t bitno)
{
	ptr->output_value[bitno / 16] &= ~(1 << (bitno % 16));
}

static void
output_bit_set(struct table_entry *ptr, uint32_t bitno)
{
	ptr->output_value[bitno / 16] |= (1 << (bitno % 16));
}

static uint32_t
input_mask_sum(struct table_entry *ptr)
{
	uint32_t size = (input_bits + 15) / 16;
	uint32_t x;
	uint32_t y;

	for (x = y = 0; x != size; x++)
		y += mbin_sumbits16(ptr->input_mask[x]);
	return (y);
}

static uint32_t
input_get(struct table_entry *ptr, uint32_t bitno)
{
	uint16_t m = (1 << (bitno % 16));

	if (ptr->input_mask[bitno / 16] & m) {
		if (ptr->input_value[bitno / 16] & m)
			return (1);
		else
			return (2);
	} else {
		return (0);
	}
}

static void
print_input(struct table_entry *entry)
{
	uint32_t x;

	for (x = 0; x != input_bits; x++) {
		switch (input_get(entry, x)) {
		case 0:
			printf("-");
			break;
		case 1:
			printf("1");
			break;
		case 2:
			printf("0");
			break;
		default:
			printf("?");
			break;
		}
	}
}

static int
do_compare(const void *_pa, const void *_pb)
{
	struct table_entry *pa = *(void **)_pa;
	struct table_entry *pb = *(void **)_pb;
	uint32_t size = ((input_bits + 15) / 16);
	int ret;

	ret = input_mask_sum(pa) - input_mask_sum(pb);
	if (ret != 0)
		return (ret);

	while (size--) {
		if (pa->input_value[size] > pb->input_value[size])
			return (1);
		else if (pa->input_value[size] < pb->input_value[size])
			return (-1);
		if (pa->input_mask[size] > pb->input_mask[size])
			return (1);
		else if (pa->input_mask[size] < pb->input_mask[size])
			return (-1);
	}
	return (0);
}

static void
input_set(struct table_entry *ptr, uint32_t bitno, uint32_t value)
{
	uint16_t m = (1 << (bitno % 16));

	switch (value) {
	case 0:
		ptr->input_mask[bitno / 16] &= ~m;
		ptr->input_value[bitno / 16] &= ~m;
		break;
	case 1:
		ptr->input_mask[bitno / 16] |= m;
		ptr->input_value[bitno / 16] |= m;
		break;
	default:
		ptr->input_mask[bitno / 16] |= m;
		ptr->input_value[bitno / 16] &= ~m;
		break;
	}
}

static void
do_sort_xor(phead_t *phead, uint8_t remove)
{
	struct table_entry *ptr;
	struct table_entry **array;
	uint32_t count;
	uint32_t osize = (output_bits + 15) / 16;
	uint32_t x;
	uint32_t y;
	uint16_t sum;

	count = 0;
	TAILQ_FOREACH(ptr, phead, entry)
	    count++;
	if (count == 0)
		return;

	array = alloca(sizeof(array[0]) * count);

	count = 0;
	TAILQ_FOREACH(ptr, phead, entry)
	    array[count++] = ptr;

	TAILQ_INIT(phead);

	qsort(array, count, sizeof(array[0]), &do_compare);

	for (x = 1; x != count; x++) {
		if (do_compare(&array[x], &array[x - 1]) == 0) {
			for (y = 0; y != osize; y++) {
				array[x]->output_value[y] ^= array[x - 1]->output_value[y];
			}
			free(array[x - 1]);
			array[x - 1] = NULL;
		} else if (remove) {
			sum = 0;
			for (y = 0; y != osize; y++)
				sum |= array[x - 1]->output_value[y];
			if (sum == 0) {
				free(array[x - 1]);
				array[x - 1] = NULL;
			}
		}
	}

	if (remove) {
		sum = 0;
		for (y = 0; y != osize; y++)
			sum |= array[x - 1]->output_value[y];
		if (sum == 0) {
			free(array[x - 1]);
			array[x - 1] = NULL;
		}
	}
	for (x = 0; x != count; x++) {
		if (array[x] == NULL)
			continue;
		TAILQ_INSERT_TAIL(phead, array[x], entry);
	}
}

static void
do_sort_add(phead_t *phead, uint8_t remove)
{
	struct table_entry *ptr;
	struct table_entry **array;
	uint32_t count;
	uint32_t x;
	uint32_t y;

	count = 0;
	TAILQ_FOREACH(ptr, phead, entry)
	    count++;
	if (count == 0)
		return;

	array = alloca(sizeof(array[0]) * count);

	count = 0;
	TAILQ_FOREACH(ptr, phead, entry)
	    array[count++] = ptr;

	TAILQ_INIT(phead);

	qsort(array, count, sizeof(array[0]), &do_compare);

	for (x = 1; x != count; x++) {
		if (do_compare(&array[x], &array[x - 1]) == 0) {
			array[x]->output_d64 += array[x - 1]->output_d64;
			free(array[x - 1]);
			array[x - 1] = NULL;
		} else if (remove) {
			if (array[x - 1]->output_d64 == 0.0) {
				free(array[x - 1]);
				array[x - 1] = NULL;
			}
		}
	}
	if (remove && array[x - 1]->output_d64 == 0.0) {
		free(array[x - 1]);
		array[x - 1] = NULL;
	}
	for (x = 0; x != count; x++) {
		if (array[x] == NULL)
			continue;
		TAILQ_INSERT_TAIL(phead, array[x], entry);
	}
}

static void
do_sort_or(phead_t *phead, uint8_t remove)
{
	struct table_entry *ptr;
	struct table_entry **array;
	uint32_t count;
	uint32_t osize = (output_bits + 15) / 16;
	uint32_t x;
	uint32_t y;
	uint16_t sum;

	count = 0;
	TAILQ_FOREACH(ptr, phead, entry)
	    count++;
	if (count == 0)
		return;

	array = alloca(sizeof(array[0]) * count);

	count = 0;
	TAILQ_FOREACH(ptr, phead, entry)
	    array[count++] = ptr;

	TAILQ_INIT(phead);

	qsort(array, count, sizeof(array[0]), &do_compare);

	for (x = 1; x != count; x++) {
		if (do_compare(&array[x], &array[x - 1]) == 0) {
			for (y = 0; y != osize; y++) {
				array[x]->output_value[y] |= array[x - 1]->output_value[y];
			}
			free(array[x - 1]);
			array[x - 1] = NULL;
		} else if (remove) {
			sum = 0;
			for (y = 0; y != osize; y++)
				sum |= array[x - 1]->output_value[y];
			if (sum == 0) {
				free(array[x - 1]);
				array[x - 1] = NULL;
			}
		}
	}
	if (remove) {
		sum = 0;
		for (y = 0; y != osize; y++)
			sum |= array[x - 1]->output_value[y];
		if (sum == 0) {
			free(array[x - 1]);
			array[x - 1] = NULL;
		}
	}
	for (x = 0; x != count; x++) {
		if (array[x] == NULL)
			continue;
		TAILQ_INSERT_TAIL(phead, array[x], entry);
	}
}

static int
compress_try(phead_t *phead, struct table_entry **pxor, uint32_t t, uint32_t u, uint32_t bitno)
{
	static const uint8_t table[3][3] = {
		{0, 2, 1},
		{2, 0, 0},
		{1, 0, 0}
	};
	struct table_entry *pnew;
	uint32_t diffs = 0;
	uint32_t loc[2] = {0, 0};
	uint32_t v;
	uint8_t a, b, c, d;

	for (v = 0; v != input_bits; v++) {
		a = input_get(pxor[t], v);
		b = input_get(pxor[u], v);
		if (a != b) {
			diffs++;
			loc[1] = loc[0];
			loc[0] = v;
		}
	}
	switch (diffs) {
	case 1:
		c = table[input_get(pxor[t], loc[0])][input_get(pxor[u], loc[0])];
		pnew = alloc_new_table_entry(pxor[t], bitno);
		input_set(pnew, loc[0], c);
		TAILQ_INSERT_TAIL(phead, pnew, entry);
		output_bit_clr(pxor[t], bitno);
		output_bit_clr(pxor[u], bitno);
		return (1);
	case 2:
		a = input_get(pxor[t], loc[1]);
		b = input_get(pxor[t], loc[0]);
		c = input_get(pxor[u], loc[1]);
		d = input_get(pxor[u], loc[0]);

		if (a != 0 && b != 0 && c != 0 && d != 0) {
			pnew = alloc_new_table_entry(pxor[t], bitno);
			input_set(pnew, loc[1], 1);
			input_set(pnew, loc[0], 0);
			TAILQ_INSERT_TAIL(phead, pnew, entry);
			pnew = alloc_new_table_entry(pxor[u], bitno);
			input_set(pnew, loc[1], 0);
			input_set(pnew, loc[0], (a == b) ? 2 : 1);
			TAILQ_INSERT_TAIL(phead, pnew, entry);
			output_bit_clr(pxor[t], bitno);
			output_bit_clr(pxor[u], bitno);
			return (1);
		}
		break;
	default:
		break;
	}
	return (0);
}

static int
compress_sub(phead_t *phead, uint32_t bitno)
{
	struct table_entry *ptr;
	struct table_entry **pxor;
	uint32_t x, y, z, t, u;
	uint32_t xor_count;
	uint32_t sby;
	uint32_t sbx;
	int loop = 0;

	do_sort_xor(phead, 1);

	xor_count = 0;
	TAILQ_FOREACH(ptr, phead, entry)
	    xor_count++;

	if (xor_count <= 1)
		return (0);

	pxor = alloca(sizeof(pxor[0]) * xor_count);

	z = 0;
	TAILQ_FOREACH(ptr, phead, entry)
	    pxor[z++] = ptr;

	for (x = 0; x != xor_count;) {
		if (output_bit_get(pxor[x], bitno) == 0) {
			x++;
			continue;
		}
		sby = sbx = input_mask_sum(pxor[x]);
		for (y = x + 1; y != xor_count; y++) {
			if (output_bit_get(pxor[y], bitno) == 0)
				continue;
			sby = input_mask_sum(pxor[y]);
			if (sbx != sby)
				break;
		}
		for (t = x; t != y; t++) {
			if (output_bit_get(pxor[t], bitno) == 0)
				continue;
			for (u = t + 1; u != y; u++) {
				if (output_bit_get(pxor[u], bitno) == 0)
					continue;
				if (compress_try(phead, pxor, t, u, bitno)) {
					loop = 1;
					break;
				}
			}
		}
		if (y == xor_count)
			break;
		for (z = y + 1; z != xor_count; z++) {
			if (output_bit_get(pxor[z], bitno) == 0)
				continue;
			if (sby != input_mask_sum(pxor[z]))
				break;
		}
		if ((sbx + 1) != sby) {
			x = y;
			continue;
		}
		for (t = x; t != y; t++) {
			if (output_bit_get(pxor[t], bitno) == 0)
				continue;
			for (u = y; u != z; u++) {
				if (output_bit_get(pxor[u], bitno) == 0)
					continue;
				if (compress_try(phead, pxor, t, u, bitno)) {
					loop = 1;
					break;
				}
			}
		}
		x = y;
	}
	return (loop);
}

static void
compress(phead_t *phead, uint32_t bitno)
{
	while (compress_sub(phead, bitno));
}

static void
usage(void)
{
	fprintf(stderr,
	    "Usage: hpspresso [-h] [-r] [-c] [-v] [-x] [-s] [-S] [-o] [-b <num>] [-d <num>] [-m <num>]\n"
	    "\t" "-c	set to compress result" "\n"
	    "\t" "-d <n>	subdivide the input variable by <n>\n"
	    "\t" "-b <n>	set number of start bits to <n>\n"
	    "\t" "-m <n>	set modulus to <n>\n"
	    "\t" "-o	set to assume AND-XOR instead of OR-XOR output" "\n"
	    "\t" "-r	set to verify full range" "\n"
	    "\t" "-S	set to use sumbits for output" "\n"
	    "\t" "-s	solve slowly, repeat to increase" "\n"
	    "\t" "-v	set to verify result" "\n"
	    "\t" "-x	set to assume XOR input" "\n"
	    "\t" "-h	show help message" "\n"
	    );
	exit(EX_USAGE);
}

int
main(int argc, char **argv)
{
	struct table_entry *entry;
	struct table_entry *check;
	uint32_t order;
	uint32_t bitno;
	uint32_t num;
	int ch;

	fp = stdin;

	while ((ch = getopt(argc, argv, "b:cvxrhsod:Sm:")) > 0) {
		switch (ch) {
		case 'm':
			do_mod = atoi(optarg);
			break;
		case 'b':
			do_skip = atoi(optarg);
			break;
		case 'd':
			do_subdivide = atoi(optarg);
			break;
		case 'c':
			do_compress = 1;
			break;
		case 'r':
			do_full_range = 1;
			break;
		case 'o':
			do_or = 1;
			do_sumbits = 0;
			break;
		case 'v':
			do_verify = 1;
			break;
		case 'x':
			do_xor = 1;
			break;
		case 's':
			do_slow++;
			break;
		case 'S':
			do_or = 0;
			do_sumbits = 1;
			break;
		default:
			usage();
		}
	}
	TAILQ_INIT(&head);
	TAILQ_INIT(&rhead);

	parse_header();
	parse_contents();

	if (do_float)
		do_sort_add(&head, 0);
	else if (do_xor)
		do_sort_xor(&head, 0);
	else
		do_sort_or(&head, 0);

#if 0
	TAILQ_FOREACH(entry, &head, entry) {
		print_input_value(entry->input_value);
		printf(" ");
		print_output(entry);
		if (do_float)
			printf(" # ADD\n");
		else
			printf(" # XOR\n");
	}
#endif
	if (do_float) {
		try_solve_d64();
		printf("# Sorting\n");
		do_sort_add(&rhead, 1);
	} else {
		for (bitno = 0; bitno != output_bits; bitno++) {
			printf("# Progress %d / %d\n", bitno, output_bits);
			try_solve_32(bitno);
		}
		if (do_compress) {
			printf("# Compressing\n");
			for (bitno = 0; bitno != output_bits; bitno++)
				compress(&rhead, bitno);
		} else {
			printf("# Sorting\n");
			do_sort_xor(&rhead, 1);
		}
	}
	printf(".i %u\n.o %u\n", input_bits, output_bits);

	num = 0;
	TAILQ_FOREACH(entry, &rhead, entry)
	    num++;
	printf(".p %u # ", num);

	if (do_float == 0) {
		for (bitno = 0; bitno != output_bits; bitno++) {
			num = 0;
			TAILQ_FOREACH(entry, &rhead, entry) {
				if (output_bit_get(entry, bitno))
					num++;
			}
			printf("%u ", num);
		}
	}
	printf("\n");

	TAILQ_FOREACH(entry, &rhead, entry) {
		print_input(entry);
		printf(" ");
		print_output(entry);
		if (do_float)
			printf(" # ADD\n");
		else
			printf(" # XOR\n");
	}
	printf(".e\n");

	if (do_full_range) {
		if (do_float) {
			check = alloc_new_table_entry(NULL, 0);
			do {
				double z = 0;

				print_input_value(check->input_value);
				printf(" ");

				TAILQ_FOREACH(entry, &rhead, entry) {
					z += entry->output_d64 * func(check->input_value,
					    entry->input_value, entry->input_mask);
				}
				printf("%e\n", z);
			} while (!increment(check->input_value, check->input_mask));
			free(check);
		} else {
			check = alloc_new_table_entry(NULL, 0);
			do {
				print_input_value(check->input_value);
				printf(" ");
				for (bitno = 0; bitno != output_bits; bitno++) {
					uint16_t m = (1 << (bitno % 16));
					uint32_t z = 0;

					TAILQ_FOREACH(entry, &rhead, entry) {
						if (entry->output_value[bitno / 16] & m) {
							if (func(check->input_value,
							    entry->input_value, entry->input_mask))
								z ^= 1;
						}
					}
					printf("%d", z);
				}
				printf("\n");
			} while (!increment(check->input_value, check->input_mask));
			free(check);
		}
	} else if (do_verify) {
		int failed = 0;

		if (do_float) {
			TAILQ_FOREACH(check, &head, entry) {
				do {
					double z = 0;
					double y = check->output_d64;

					print_input_value(check->input_value);
					printf(" ");

					TAILQ_FOREACH(entry, &rhead, entry) {
						z += entry->output_d64 * func(check->input_value,
						    entry->input_value, entry->input_mask);
					}
					if ((int64_t)(fabs(z) + 0.5) != (int64_t)(fabs(y) + 0.5)) {
						printf("%e %e", z, y);
						failed = 1;
					} else
						printf("%e", y);
					printf("\n");
				} while (!increment(check->input_value, check->input_mask));
			}
		} else {
			TAILQ_FOREACH(check, &head, entry) {
				do {
					print_input_value(check->input_value);
					printf(" ");
					for (bitno = 0; bitno != output_bits; bitno++) {
						uint16_t m = (1 << (bitno % 16));
						uint32_t z = 0;
						uint32_t y = (check->output_value[bitno / 16] & m) ? 1 : 0;

						TAILQ_FOREACH(entry, &rhead, entry) {
							if (entry->output_value[bitno / 16] & m) {
								if (func(check->input_value,
								    entry->input_value, entry->input_mask))
									z ^= 1;
							}
						}
						if (z != y && (check->output_mask[bitno / 16] & m) != 0) {
							failed = 1;
							printf("X");
						} else {
							printf("%d", z);
						}
					}
					printf("\n");
				} while (!increment(check->input_value, check->input_mask));
			}
		}
		if (failed == 0)
			printf("SUCCESS\n");
		else
			printf("FAILURE\n");
	}
	return (0);
}
