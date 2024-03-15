/*
 * bignum.c
 *
 * Routines for big number arithmetic
 *
 * (C) 2024, Kenneth Roe
 *
 * GNU Affero General Public License
 */
#include <stdio.h>
#include <stdlib.h>
#include "globals.h"

static void adjust(unsigned *n)
{
    unsigned tail ;
    unsigned pos ;

    pos = n[0] ;
    if (n[pos]==0xffffffff) {
        tail = 0xffffffff ;
    } else {
        tail = 0 ;
    }
    while (pos > 0 && n[pos]==tail) --pos ;
    if (((n[pos] & 0x80000000) && tail==0xffffffff) ||
        (((n[pos] & 0x80000000)==0) && tail==0)) {
        n[0] = pos ;
    } else if (pos < n[0]-1) {
        n[0] = pos + 1 ;
    }
    if (n[0]==0) n[0] = 1 ;
}

int _th_big_equal(unsigned *n1, unsigned *n2)
{
    unsigned i ;

    for (i = 0; i <= *n1; ++i) {
        if (n1[i] != n2[i]) return 0 ;
    }
    return 1 ;
}

int _th_big_less(unsigned *n1, unsigned *n2)
{
    int carry = 0 ;
    unsigned i ;
    unsigned n1_len = *n1 ;
    unsigned n2_len = *n2 ;
    unsigned max_len = (n1_len < n2_len)?n2_len:n1_len ;
    unsigned add ;
    unsigned res ;

    ++n1 ; ++n2 ;
    for (i = 0; i < n1_len && i < n2_len; ++i) {
        res = *n1-*n2-carry ;
        if (carry) {
            carry = (res >= *n1)?1:0 ;
        } else {
            carry = (res > *n1)?1:0 ;
        }
        ++n1 ; ++n2 ;
    }
    if (n1_len < n2_len) {
        --n1 ;
        if (*n1 & 0x80000000) {
            add = 0xffffffff ;
        } else {
            add = 0 ;
        }
        while (i < n2_len) {
            res = add - *n2 - carry ;
            carry = (*n2 + carry > add)?1:0;
            ++n2 ; ++i ;
        }
    } else {
        --n2 ;
        if (*n2 & 0x80000000) {
            add = 0xffffffff ;
        } else {
            add = 0 ;
        }
        while (i < n1_len) {
            res = *n1 - add - carry ;
            carry = (*n1 > carry + add)?1:0;
            ++n1 ; ++i ;
        }
    }
    return (res&0x80000000) ;
}

int _th_big_is_negative(unsigned *num)
{
    unsigned *last = num + *num ;

    return (*last&0x80000000) ;
}

static void complement(unsigned *num)
{
    unsigned count = *num ;
    unsigned *start = num ;

    ++num ;
    while (count > 0) {
        *num = *num ^ 0xffffffff ;
        --count ;
        ++num ;
    }
    num = start ;
    count = *num ;
    ++num ;
    while (count > 0) {
        --count ;
        ++*num ;
        if (*num) return ;
        ++num ;
    }
    *num = 1 ;
    ++*start ;
}

void _th_big_print_hex(unsigned *big)
{
    unsigned count ;

    count = *big++ ;

    while(count--) {
        printf(" %x", *big++) ;
    }
    printf("\n") ;
}

unsigned buffer_size ;

unsigned *accumulate ;
unsigned *dividend ;
unsigned *result ;

#define BUFFER_INCREMENT 30

void _th_init_bignum()
{
    buffer_size = BUFFER_INCREMENT ;

    accumulate = (unsigned *)malloc(sizeof(unsigned) * buffer_size) ;
    dividend = (unsigned *)malloc(sizeof(unsigned) * buffer_size) ;
    result = (unsigned *)malloc(sizeof(unsigned) * buffer_size) ;
}

static void check_buffer(unsigned size)
{
    if (size <= buffer_size) return ;

    buffer_size = size ;

    accumulate = (unsigned *)realloc(accumulate, sizeof(unsigned) * buffer_size) ;
    dividend = (unsigned *)realloc(dividend, sizeof(unsigned) * buffer_size) ;
    result = (unsigned *)realloc(result, sizeof(unsigned) * buffer_size) ;
}

static void _add(unsigned *res, unsigned *n1, unsigned *n2)
{
    int carry = 0 ;
    unsigned i ;
    unsigned n1_len = *n1 ;
    unsigned n2_len = *n2 ;
    unsigned max_len = (n1_len < n2_len)?n2_len:n1_len ;
    unsigned *ret ;
    unsigned add, comp ;

    ++n1 ; ++n2 ;
    ret = res ;
    *res++ = max_len ;
    for (i = 0; i < n1_len && i < n2_len; ++i) {
        comp = *n1 ;
        *res = *n1+*n2+carry ;
        if (carry) {
            carry = (*res <= comp || *res <= *n2)?1:0 ;
        } else {
            carry = (*res < comp || *res < *n2)?1:0 ;
        }
        ++res ; ++n1 ; ++n2 ;
    }
    if (n1_len < n2_len) {
        --n1 ;
        if (*n1 & 0x80000000) {
            add = 0xffffffff ;
        } else {
            add = 0 ;
        }
        while (i < n2_len) {
            comp = *n2 ;
            *res = add + *n2 + carry ;
            if (carry) {
                carry = (*res <= add || *res <= comp)?1:0 ;
            } else {
                carry = (*res < add || *res < comp)?1:0 ;
            }
            ++res ; ++n2 ; ++i ;
        }
    } else {
        --n2 ;
        if (*n2 & 0x80000000) {
            add = 0xffffffff ;
        } else {
            add = 0 ;
        }
        while (i < n1_len) {
            comp = *n1 ;
            *res = add + *n1 + carry ;
            if (carry) {
                carry = (*res <= add || *res <= comp)?1:0 ;
            } else {
                carry = (*res < add || *res < comp)?1:0 ;
            }
            ++res ; ++n1 ; ++i ;
        }
    }
    adjust(ret) ;
}

static void _sub(unsigned *res, unsigned *n1, unsigned *n2)
{
    int carry = 0 ;
    unsigned i ;
    unsigned n1_len = *n1 ;
    unsigned n2_len = *n2 ;
    unsigned max_len = (n1_len < n2_len)?n2_len:n1_len ;
    unsigned *ret ;
    unsigned add, comp ;

    ++n1 ; ++n2 ;
    ret = res ;
    *res++ = max_len ;
    for (i = 0; i < n1_len && i < n2_len; ++i) {
        comp = *n1 ;
        *res = *n1-*n2-carry ;
        if (carry) {
            carry = (*res >= comp)?1:0 ;
        } else {
            carry = (*res > comp)?1:0 ;
        }
        ++res ; ++n1 ; ++n2 ;
    }
    if (n1_len < n2_len) {
        --n1 ;
        if (*n1 & 0x80000000) {
            add = 0xffffffff ;
        } else {
            add = 0 ;
        }
        while (i < n2_len) {
            *res = add - *n2 - carry ;
            carry = (carry+*n2>add)?1:0 ;
            if (carry) {
                carry = (*res >= add)?1:0 ;
            } else {
                carry = 0 ;
            }
            ++res ; ++n2 ; ++i ;
        }
    } else {
        --n2 ;
        if (*n2 & 0x80000000) {
            add = 0xffffffff ;
        } else {
            add = 0 ;
        }
        while (i < n1_len) {
            comp = *n1 ;
            *res = *n1 - add - carry ;
            carry = (add+carry > *n1)?1:0 ;
            ++res ; ++n1 ; ++i ;
        }
    }
    adjust(ret) ;
}

unsigned *_th_big_add(unsigned *a, unsigned *b)
{
    if (*a > *b) {
        check_buffer(*a+1) ;
    } else {
        check_buffer(*b+1) ;
    }
    _add(result,a,b) ;
    return result ;
}

unsigned *_th_big_sub(unsigned *a, unsigned *b)
{
    if (*a > *b) {
        check_buffer(*a+1) ;
    } else {
        check_buffer(*b+1) ;
    }
    _sub(result,a,b) ;
    return result ;
}

static void add_word(unsigned half_pos, unsigned word)
{
    unsigned res, op1, op2 ;

    if (half_pos & 1) {
        half_pos /= 2 ;
        op1 = word << 16 ;
        op2 = word >> 16 ;
        res = accumulate[++half_pos] + op1 ;
        accumulate[half_pos] = res ;
        if (res < op1) {
            ++op2 ;
        }
        res = accumulate[++half_pos] + op2 ;
        accumulate[half_pos] = res ;
    } else {
        half_pos /= 2 ;
        res = accumulate[++half_pos] + word ;
        accumulate[half_pos] = res ;
    }
    if (res < word) {
        while(half_pos < accumulate[0] && accumulate[++half_pos]==0xffffffff) {
            ++accumulate[half_pos] ;
        }
    }
}

unsigned *_th_big_multiply(unsigned *a, unsigned *b)
{
    unsigned size = a[0]+b[0] ;
    unsigned i, j ;
    unsigned res, op1, op2 ;
    int compl = 0 ;

    check_buffer(size) ;

    for (i = 0; i <= *a; ++i) dividend[i] = a[i] ;

    for (i = 0; i <= *b; ++i) result[i] = b[i] ;

    if (_th_big_is_negative(dividend)) {
        compl = 1-compl ;
        complement(dividend) ;
    }
    if (_th_big_is_negative(result)) {
        compl = 1-compl ;
        complement(result) ;
    }

    for (i = 1; i < size; ++i) {
        accumulate[i] = 0 ;
    }
    accumulate[0] = size-1 ;

    for (i = 0 ; i < dividend[0]; ++i) {
        for (j = 0; j < result[0]; ++j) {
             op1 = dividend[i+1] & 0xffff ;
             op2 = result[j+1] & 0xffff ;
             res = op1 * op2 ;
             add_word((i+j)*2,res) ;

             op1 = (dividend[i+1] >> 16) & 0xffff ;
             op2 = result[j+1] & 0xffff ;
             res = op1 * op2 ;
             add_word((i+j)*2+1,res) ;

             op1 = dividend[i+1] & 0xffff ;
             op2 = (result[j+1] >> 16) & 0xffff ;
             res = op1 * op2 ;
             add_word((i+j)*2+1,res) ;

             op1 = (dividend[i+1] >> 16) & 0xffff ;
             op2 = (result[j+1] >> 16) & 0xffff ;
             res = op1 * op2 ;
             add_word((i+j)*2+2,res) ;
        }
    }

    if (compl) complement(accumulate) ;

    adjust(accumulate) ;
    return accumulate ;
}

void left_shift(unsigned *value)
{
    unsigned i, carry, carry2 ;

    if (value[*value]&0x80000000) {
        ++*value ;
        value[*value] = 0 ;
    }
    carry = 0 ;
    for (i = 1; i <= *value; ++i) {
        carry2 = carry ;
        carry = value[i]&0x80000000 ;
        value[i] = value[i]<<1 ;
        if (carry2) ++value[i] ;
    }
    if (value[*value]&0x80000000) {
        ++*value ;
        value[*value] = 0 ;
    }
}

void right_shift(unsigned *value)
{
    unsigned i ;

    for (i = 1; i < *value; ++i) {
         value[i] = value[i]>>1;
         if (value[i+1]&1) value[i] |= 0x80000000 ;
    }
    value[i] = value[i]>>1;
    if (*value > 1) {
        if (value[*value]==0 && (value[*value-1]&0x80000000)==0) --*value ;
        if (value[*value]==0xffffffff && value[*value-1]&0x80000000) --*value ;
    }
}

static int _raw_divide(unsigned *numerator, unsigned *denominator)
{
    unsigned i ;
    int compl_res = 0 ;
    int compl_accumulate = 0 ;
    int divisor_count = 0 ;

    if (*denominator > *numerator) {
        accumulate[0] = 1 ;
        accumulate[1] = 0 ;
        return 0 ;
    }

    if (denominator[0]==1 && denominator[1] == 0) return 1 ;
    check_buffer(*numerator+2) ;

    for (i = 0; i <= *numerator; ++i) {
        accumulate[i] = numerator[i] ;
    }
    if (_th_big_is_negative(accumulate)) {
        complement(accumulate) ;
        compl_res = 1 ;
        compl_accumulate = 1 ;
    }
    for (i = 0; i <= *denominator; ++i) {
        dividend[i] = denominator[i] ;
    }
    if (_th_big_is_negative(dividend)) {
        complement(dividend) ;
        compl_res = 1-compl_res ;
    }
    while(_th_big_less(dividend,accumulate)) {
        left_shift(dividend) ;
        ++divisor_count ;
    }

    for (i = 1; i <= (unsigned)divisor_count / 32 + 1; ++i) {
        result[i] = 0 ;
    }
    result[0] = divisor_count / 32 + 1 ;

    while(divisor_count >= 0) {
        if (!_th_big_less(accumulate,dividend)) {
            result[divisor_count/32+1] |= 1<<(divisor_count%32) ;
            _sub(accumulate,accumulate,dividend) ;
        }
        right_shift(dividend) ;
        --divisor_count;
    }

    if (compl_res) complement(result) ;
    if (compl_accumulate) complement(accumulate) ;
	return 0;
}

unsigned *_th_big_divide(unsigned *a, unsigned *b)
{
    _raw_divide(a,b) ;
    adjust(result) ;
    return result ;
}

unsigned *_th_big_mod(unsigned *a, unsigned *b)
{
    _raw_divide(a,b) ;
    adjust(accumulate) ;
    return accumulate ;
}

unsigned *_th_big_copy(int space, unsigned *n)
{
    unsigned *s = (unsigned *)_th_alloc(space,sizeof(unsigned) * (*n+1)) ;
    unsigned i ;

    for (i = 0; i <= *n; ++i) s[i] = n[i] ;

    return s ;
}

