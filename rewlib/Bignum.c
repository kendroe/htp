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
#include "Globals.h"

int bignum_print = 1;

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
    unsigned carry = 0 ;
    unsigned i ;
    unsigned n1_len = *n1 ;
    unsigned n2_len = *n2 ;
    unsigned max_len = (n1_len < n2_len)?n2_len:n1_len ;
    unsigned add ;
    unsigned res ;
    unsigned comp1, comp2;

    if (n1[0]==1 && n2[0]==1) {
        return ((int)n1[1]) < ((int)n2[1]);
    }

#ifdef PRINT_BIGNUM
	if (bignum_print) {
	    printf("_th_big_less of");
	    for (i =0; i < *n1; ++i) printf(" %d", n1[i+1]);
	    printf(" and");
	    for (i =0; i < *n2; ++i) printf(" %d", n2[i+1]);
        printf("\n");
	}
#endif

    ++n1 ; ++n2 ;
    for (i = 0; i < n1_len && i < n2_len; ++i) {
        comp1 = *n1; comp2 = *n2;
        res = comp1-comp2-carry ;
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
            comp1 = add = 0xffffffff ;
        } else {
            comp1 = add = 0 ;
        }
        while (i < n2_len) {
            comp2 = *n2;
            res = add - comp2 - carry ;
            if (carry) {
                carry = (res >= add)?1:0;
            } else {
                carry = (res > add)?1:0;
            }
            ++n2 ; ++i ;
        }
    } else {
        --n2 ;
        if (*n2 & 0x80000000) {
            comp2 = add = 0xffffffff ;
        } else {
            comp2 = add = 0 ;
        }
        while (i < n1_len) {
            comp1 = *n1;
            res = comp1 - add - carry ;
            if (carry) {
                carry = (res >= *n1)?1:0 ;
            } else {
                carry = (res > *n1)?1:0 ;
            }
            ++n1 ; ++i ;
        }
    }

    if ((comp1 & 0x80000000)!=(comp2 &0x80000000) &&
        (comp1 & 0x80000000)!=(res & 0x80000000)) {
#ifdef PRINT_BIGNUM
		if (bignum_print) printf("    Result: %d\n", !(res&0x80000000));
#endif
			return !(res&0x80000000);
    } else {
#ifdef PRINT_BIGNUM
		if (bignum_print) printf("    Result: %d\n", (res&0x80000000));
#endif
		return (res&0x80000000) ;
    }
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
    unsigned i;

    for (i = 1; i <= *num; ++i) {
        if (num[i]) goto cont;
    }
    return;
cont:
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
        if (*num) {
            if (count==0 && *num==0x80000000) {
                ++*start;
                ++num;
                *num = 0;
            }
            return ;
        }
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
unsigned *power ;

#define BUFFER_INCREMENT 30

void _th_init_bignum()
{
    buffer_size = BUFFER_INCREMENT ;

    accumulate = (unsigned *)MALLOC(sizeof(unsigned) * buffer_size) ;
    dividend = (unsigned *)MALLOC(sizeof(unsigned) * buffer_size) ;
    result = (unsigned *)MALLOC(sizeof(unsigned) * buffer_size) ;
    power = (unsigned *)MALLOC(sizeof(unsigned) * buffer_size) ;
}

static void check_buffer(unsigned size)
{
    if (size <= buffer_size) return ;

    buffer_size = size ;

    accumulate = (unsigned *)REALLOC(accumulate, sizeof(unsigned) * buffer_size) ;
    dividend = (unsigned *)REALLOC(dividend, sizeof(unsigned) * buffer_size) ;
    result = (unsigned *)REALLOC(result, sizeof(unsigned) * buffer_size) ;
    power = (unsigned *)REALLOC(power, sizeof(unsigned) * buffer_size) ;
}

unsigned *_th_complement(unsigned *num)
{
    int i;
    check_buffer(*num+2);

    for (i = 0; i <= (int)*num; ++i) {
        accumulate[i] = num[i];
    }

    complement(accumulate);

    return accumulate;
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

#ifdef PRINT_ADDS
    if (print_adds) {
        printf("n1 = %d", n1[0]);
        for (i = 1; i <= n1[0]; ++i) {
            printf(" %d", n1[i]);
        }
        printf("\n");
        printf("n2 = %d", n2[0]);
        for (i = 1; i <= n2[0]; ++i) {
            printf(" %d", n2[i]);
        }
        printf("\n");
    }
#endif

    ++n1 ; ++n2 ;
    ret = res ;
    *res++ = max_len ;
    for (i = 0; i < n1_len && i < n2_len; ++i) {
        //printf("Adding %d and %d\n", *n1, *n2);
        comp = *n1 ;
        *res = *n1+*n2+carry ;
        if (carry) {
            carry = (*res <= comp || *res <= *n2)?1:0 ;
        } else {
            carry = (*res < comp || *res < *n2)?1:0 ;
        }
        //printf("Result %d\n", *res);
        ++res ; ++n1 ; ++n2 ;
    }
    if (n1_len < n2_len) {
        --n1 ;
        if (comp & 0x80000000) {
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
        --n2;
        --res;
        if ((comp & 0x80000000)==(add & 0x80000000) && (add & 0x80000000) != (*res & 0x80000000)) {
            ++ret[0];
            if (*res & 0x80000000) {
                res[1] = 0;
            } else {
                res[1] = 0xffffffff;
            }
        }
    } else if (n2_len < n1_len) {
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
        --n1;
        --res;
        if ((comp & 0x80000000)==(add & 0x80000000) && (comp & 0x80000000) != (*res & 0x80000000)) {
            ++ret[0];
            if (*res & 0x80000000) {
                res[1] = 0;
            } else {
                res[1] = 0xffffffff;
            }
        }
    } else {
        --n1;
        --n2;
        --res;
        //printf("comp = %d\n", comp);
        //printf("*n2 = %d\n", *n2);
        //printf("*res = %d\n", *res);
        if ((comp & 0x80000000)==(*n2 & 0x80000000) && (comp & 0x80000000) != (*res & 0x80000000)) {
            ++ret[0];
            if (*res & 0x80000000) {
                res[1] = 0;
            } else {
                res[1] = 0xffffffff;
            }
        }
    }
    //printf("ret = %d %d %d\n", ret[0], ret[1], ret[2]);
    adjust(ret) ;
    //printf("ret = %d %d %d\n", ret[0], ret[1], ret[2]);
#ifdef PRINT_ADDS
    if (print_adds) {
        printf("ret = %d", ret[0]);
        for (i = 1; i <= ret[0]; ++i) {
            printf(" %d", ret[i]);
        }
        printf("\n");
    }
#endif
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
        //printf("_sub %d %u %u %u\n", i, *n1, *n2, carry);
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
            comp = add = 0xffffffff ;
        } else {
            comp = add = 0 ;
        }
        while (i < n2_len) {
            //printf("_sub_a %d %u %u %u\n", i, add, *n2, carry);
            *res = add - *n2 - carry ;
            //carry = (carry+*n2>add)?1:0 ;
            if (carry) {
                carry = (*res >= add)?1:0 ;
            } else {
                carry = 0 ;
            }
            ++res ; ++n2 ; ++i ;
        }
        --n2;
        --res;
        if ((comp & 0x80000000)!=(*n2 & 0x80000000) && (comp & 0x80000000) != (*res & 0x80000000)) {
            ++ret[0];
            if (*res & 0x80000000) {
                res[1] = 0;
            } else {
                res[1] = 0xffffffff;
            }
        }
    } else if (n2_len < n1_len) {
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
        --n1;
        --res;
        if ((comp & 0x80000000)!=(add & 0x80000000) && (comp & 0x80000000) != (*res & 0x80000000)) {
            ++ret[0];
            if (*res & 0x80000000) {
                res[1] = 0;
            } else {
                res[1] = 0xffffffff;
            }
        }
    } else {
        --n1;
        --n2;
        --res;
        //printf("comp = %d\n", comp);
        //printf("*n2 = %d\n", *n2);
        //printf("*res = %d\n", *res);
        if ((comp & 0x80000000)!=(*n2 & 0x80000000) && (comp & 0x80000000) != (*res & 0x80000000)) {
            ++ret[0];
            if (*res & 0x80000000) {
                res[1] = 0;
            } else {
                res[1] = 0xffffffff;
            }
        }
    }
    adjust(ret) ;
}

unsigned *_th_big_add(unsigned *a, unsigned *b)
{
#ifdef PRINT_BIGNUM
	if (bignum_print && (*a > 1 || *b > 1)) {
		int i;
		printf("Adding");
	    for (i =0; i < *a; ++i) printf(" %x", a[i+1]);
	    printf(" and");
	    for (i =0; i < *b; ++i) printf(" %x", b[i+1]);
        printf("\n");
	}
#endif
	if (*a > *b) {
        check_buffer(*a+1) ;
    } else {
        check_buffer(*b+1) ;
    }
    _add(result,a,b) ;
#ifdef PRINT_BIGNUM
	if (bignum_print && *result > 1) {
		int i;
		printf("   result");
	    for (i =0; i < *result; ++i) printf(" %x", result[i+1]);
		printf("\n");
	}
#endif
	return result ;
}

unsigned *_th_big_accumulate(unsigned *a, unsigned *b)
{
    //printf("Adding a %d %d %d\n", a[0], a[1], a[2]);
    //printf("   and b %d %d %d\n", b[0], b[1], b[2]);
    if (*a > *b) {
        check_buffer(*a+1) ;
    } else {
        check_buffer(*b+1) ;
    }
    //printf("Adding a %d %d %d\n", a[0], a[1], a[2]);
    //printf("   and b %d %d %d\n", b[0], b[1], b[2]);
    _add(a,a,b) ;
    return a ;
}

unsigned *_th_big_accumulate_small(unsigned *a, int x)
{
    unsigned b[2];
    b[0] = 1;
    b[1] = x;
    //printf("Adding a %d %d %d\n", a[0], a[1], a[2]);
    //printf("   and b %d %d %d\n", b[0], b[1], b[2]);
    if (*a > *b) {
        check_buffer(*a+1) ;
    } else {
        check_buffer(*b+1) ;
    }
    //printf("Adding a %d %d %d\n", a[0], a[1], a[2]);
    //printf("   and b %d %d %d\n", b[0], b[1], b[2]);
    _add(a,a,b) ;
    return a ;
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
        word = op2;
    } else {
        half_pos /= 2 ;
        res = accumulate[++half_pos] + word ;
        accumulate[half_pos] = res ;
    }
    if (res < word) {
        while(accumulate[++half_pos]==0xffffffff && half_pos < accumulate[0]+1) {
            ++accumulate[half_pos] ;
        }
        ++accumulate[half_pos] ;
    }
}

unsigned *_th_big_multiply(unsigned *a, unsigned *b)
{
    unsigned size = a[0]+b[0] ;
    unsigned i, j ;
    unsigned res, op1, op2 ;
    int compl = 0 ;

#ifdef PRINT_BIGNUM
	if (bignum_print && (*a > 1 || *b > 1)) {
	    printf("Multiply");
		for (i = 0; i < *a; ++i) printf(" %x", a[i+1]);
		printf(" and");
		for (i = 0; i < *b; ++i) printf(" %x", b[i+1]);
		printf("\n");
	}
#endif

    check_buffer(size+2) ;

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

    for (i = 1; i < size+1; ++i) {
        accumulate[i] = 0 ;
    }
    accumulate[0] = size ;

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

#ifdef PRINT_BIGNUM
	if (bignum_print && accumulate[0] > 1) {
		printf("    Result");
		for (i = 0; i < *accumulate; ++i) printf(" %x", accumulate[i+1]);
		printf("\n");
	}
#endif

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
    int divisor_count = 1 ;
    int do_print = 0;

#ifdef PRINT_BIGNUM
	//if (bignum_print) {
		int i;
	    printf("Dividing");
	    for (i =0; i < *numerator; ++i) printf(" %x", numerator[i+1]);
	    printf(" and");
	    for (i =0; i < *denominator; ++i) printf(" %x", denominator[i+1]);
        printf("\n");
	}
#endif
	//if (denominator[1] == 10) {
	//    _zone_print("Dividing %x %x %x and %x %x %x\n",
	//	            numerator[0], numerator[1], numerator[2],
	//		    	denominator[0], denominator[1], denominator[2]);
	//}

    if (denominator[0]==1 && denominator[1] == 0) {
        int *x = 0;
        *x = 1;
        fprintf(stderr,"Divide by zero\n");
        exit(1);
        //return 1 ;
    }
    check_buffer(*numerator+2) ;

    for (i = 0; i <= *numerator; ++i) {
        accumulate[i] = numerator[i] ;
    }

    if (*denominator > *numerator) {
        result[0] = 1 ;
        result[1] = 0 ;
        return 0 ;
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
    //printf("Test dividend %d %d %d %d\n", dividend[0], dividend[1], dividend[2], dividend[3]);
    //printf("Test accumulate %d %d %d %d\n", accumulate[0], accumulate[1], accumulate[2], accumulate[3]);
    while(_th_big_less(dividend,accumulate)) {
        //printf("Before divident %d %d %d %d\n", dividend[0], dividend[1], dividend[2], dividend[3]);
        left_shift(dividend) ;       
        ++divisor_count ;
    }
    //printf("    divisor_count, dividend %d %d %d %d %d\n", divisor_count, dividend[0], dividend[1], dividend[2], dividend[3]);

	//if (denominator[1] != 10) _zone_print("count %d", divisor_count);

    for (i = 1; i <= (unsigned)divisor_count / 32 + 1; ++i) {
        result[i] = 0 ;
    }
    result[0] = divisor_count / 32 + 1 ;

    while(divisor_count > 0) {
        --divisor_count;
        if (!_th_big_less(accumulate,dividend)) {
            result[divisor_count/32+1] |= 1<<(divisor_count%32) ;
            _sub(accumulate,accumulate,dividend) ;
        }
        right_shift(dividend) ;
    }

    if (compl_res) complement(result) ;
    if (compl_accumulate) complement(accumulate) ;

	//if (denominator[1] != 10) _zone_print("Result %x %x %x", result[0], result[1], result[2]);

#ifdef PRINT_BIGNUM
	if (bignum_print) {
		int i;
	    printf("    results");
	    for (i =0; i < *result; ++i) printf(" %x", result[i+1]);
	    printf(" and");
	    for (i =0; i < *accumulate; ++i) printf(" %x", accumulate[i+1]);
        printf("\n");
	}
#endif

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

unsigned *_th_big_power(unsigned *a, unsigned *b)
{
    int i, j;

    if (b[0] > 1) {
        printf("Power overflow\n");
        exit(1);
    }
    if (b[1]==0) {
        result[0] = 1;
        result[1] = 1;
        return result;
    }
    if (b[1]&0x80000000) {
        result[0] = 1;
        result[1] = 0;
        return result;
    }
    if (b[1]==1) {
        return a;
    }
    _th_big_multiply(a,a);
    for (i = 2; i < (int)b[1]; ++i) {
        for (j = 0; j <= (int)accumulate[0]; ++j) {
            power[j] = accumulate[j];
        }
        _th_big_multiply(power,a);
    }
    return accumulate;
}

unsigned *_th_big_gcd(unsigned *x, unsigned *y)
{
    unsigned *diff ;
    static unsigned zero[] = { 1, 0 } ;

#ifdef PRINT_BIGNUM
	if (bignum_print) {
		int i;
	    printf("GCD");
	    for (i =0; i < *x; ++i) printf(" %x", x[i+1]);
	    printf(" and");
	    for (i =0; i < *y; ++i) printf(" %x", y[i+1]);
        printf("\n");
	}
#endif

    if (_th_big_is_zero(x) || _th_big_is_zero(y)) return zero ;
    if (_th_big_is_negative(x)) {
        x = _th_big_copy(REWRITE_SPACE,_th_big_sub(zero, x)) ;
    }
    if (_th_big_is_negative(y)) {
        y = _th_big_copy(REWRITE_SPACE,_th_big_sub(zero, y)) ;
    }
    if (_th_big_less(x,y)) {
        diff = _th_big_mod(y,x) ;
		if (_th_big_is_zero(diff)) {
#ifdef PRINT_BIGNUM
			if (bignum_print) {
		        int i;
	            printf("GCD result");
	            for (i =0; i < *x; ++i) printf(" %x", x[i+1]);
                printf("\n");
	        }
#endif
			return x ;
		}
        return _th_big_gcd(x,_th_big_copy(REWRITE_SPACE,diff)) ;
    } else {
        diff = _th_big_mod(x,y) ;
		if (_th_big_is_zero(diff)) {
#ifdef PRINT_BIGNUM
        	if (bignum_print) {
		        int i;
	            printf("GCD result");
	            for (i =0; i < *x; ++i) printf(" %x", x[i+1]);
                printf("\n");
	        }
#endif
			return y ;
		}
        return _th_big_gcd(_th_big_copy(REWRITE_SPACE,diff),y) ;
    }
}

