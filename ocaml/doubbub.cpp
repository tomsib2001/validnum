/****************************************************************************\
File: doubbub.cpp

This program will be published in conjunction with the paper
"Double Bubbles Minimize", by Joel Hass and Roger Schlafly,
in the Annals of Mathematics.  After publication, permission
to use for the purpose of scholarly research is hereby granted.

Last modified: Aug. 1, 1999

Contact information.

Annals of Mathematics
http://www.math.princeton.edu/~annals/web
annals@math.princeton.edu

Double bubble home page
http://math.ucdavis.edu/~hass/bubbles.html

Roger Schlafly
UC Computer Science Dept, Santa Cruz CA 95064 USA
http://schlafly.homepage.com
http://bbs.cruzio.com/~schlafly
real@ieee.org

Joel Hass
UC Math Dept, Davis CA 95616 USA
http://math.ucdavis.edu/~hass
hass@math.ucdavis.edu

Instructions for compiling and running.

On UNIX systems there is usually a C++ compiler called "CC". 
You can compile doubbub.cpp and name the output executable "doubbub" with:

	CC -o doubbub doubbub.cpp

On some systems you have to insert the switch "-lm" to link in the
math library.  If the GNU C++ compiler is available, it is usually
better, and you can compile with:

	g++ -o doubbub doubbub.cpp

Linux systems will generally have the GNU C++ compiler.

On a PC (ie, Microsoft/Intel platform), you can create a "console
application" with Microsoft Visual C++.  On Borland C++, you can
do the same thing, or just compile with "bcc32 doubbub".  You can also 
use the 16-bit compiler, or whatever optimization switches you please.

To run, just type "doubbub all" at a command prompt. If it is set up
correctly, the program will run for 8 to 60 seconds, on a typical 1999
PC or workstation, and eventually will announce that all torus bubbles
are rejected. Otherwise, you should get some sort of error message 
indicating what the problem is. The program keeps track of the number
of compuations performed.  On all machines we have tested this has led 
to the following totals, which the program will print if it gets
consistent results:
 
Finished calculations, successes = 15016, integrals = 51256, dY = 0.00098

The program has been tested on  Wintel, Sun, HP, SGI, Linux/Intel,
and Macintosh platforms, with identical results.  Variations in
computer model, OS version, and installation options may be such
that changes are required to compile this program.
\****************************************************************************/

#ifndef __cplusplus
#error Must use C++.
#endif

#include <stdio.h>
#include <stdlib.h>
#include <math.h>	// for sqrt()
#include <time.h>
#include <assert.h>

typedef double real;	// 'double' also works fine

/****************************************************************************\
System dependent code.
\****************************************************************************/

#if	defined(_MSC_VER)
#define Platform "Wintel, using Microsoft C++"

// this code works for Microsoft or Borland C++
#include <float.h>
#define fpclear()	_clear87()
#define round_down()	_control87(RC_DOWN,MCW_RC);
#define round_up()	_control87(RC_UP,MCW_RC);
#define round_near()	_control87(RC_NEAR,MCW_RC);
#define round_chop()	_control87(RC_CHOP,MCW_RC);
#define maskall()	_fpreset();_control87(MCW_EM,MCW_EM);
#define status()	(_status87() & SW_INVALID+SW_ZERODIVIDE\
			+SW_OVERFLOW+SW_UNDERFLOW)

real infinity()
{
	long a = 0x7f800000l;
	return * (float *) &a;
}

real fsqrt(real x)
{
	// library routine rounds to nearest only
	__asm	fld x
	__asm	fsqrt
	__asm	fstp x
	return x;
}

#endif

#if	defined(__BORLANDC__)
#define Platform "Wintel, using Borland C++"
#include <float.h>
// similar to the above, but with some Intel/Borland optimizations

int status()
{
	asm	fstsw	ax
	asm	and	ax, 13
	return _AX;
}

// all traps masked
// to unmask, change F to 2
static unsigned short ctrl_up   = 0x1B7F;
static unsigned short ctrl_down = 0x177F;
static unsigned short ctrl_near = 0x137F;

#define round_down()	asm	fldcw	ctrl_down
#define round_up()	asm	fldcw	ctrl_up
#define round_near()	asm	fldcw	ctrl_near
#define maskall()	_fpreset(),_control87(MCW_EM,MCW_EM)
#define infinity()	1e9999

real fsqrt(real x)
{
	asm	fld x
	asm	fsqrt
	asm	fstp x
	return x;
}

#endif

#if	defined(sun) || defined(__sgi)
#if	defined(sun)
	#define Platform "Sun Unix"
#else
	#define Platform "SGI Unix"
#endif

#include <ieeefp.h>

#define fpclear()	fpsetsticky(FP_X_CLEAR)
#define round_near()	fpsetround(FP_RN)
#define round_down()	fpsetround(FP_RM)
#define round_up()	fpsetround(FP_RP)
#define round_chop()	fpsetround(FP_RZ)
#define status()	(fpgetsticky() & FP_X_INV+FP_X_DZ+FP_X_OFL+FP_X_UFL)
#define maskall()	fpsetmask(FP_X_CLEAR)
#define FP_X_CLEAR	0
#define bool int

real infinity()
{
	long a = 0x7f800000l;
	return * (float *) &a;
}

real fsqrt(real x)
{
	// assume library doesn't change rounding mode
	return sqrt(x);
}

#endif

#if	defined(__hpux) || defined(__MWERKS__)
#if	defined(__hpux)
#define Platform "HP Unix"
#else
#define Platform "Macintosh"
#endif

#include <fenv.h>

#define fpclear()	feclearexcept(FE_ALL_EXCEPT)
#define round_near()	fesetround(FE_TONEAREST)
#define round_down()	fesetround(FE_DOWNWARD)
#define round_up()	fesetround(FE_UPWARD)
#define round_chop()	fesetround(FE_TOWARDZERO)
#define status()	fetestexcept(FE_DIVBYZERO+FE_INVALID+\
			FE_OVERFLOW+FE_UNDERFLOW)
#define maskall()	0
#define infinity()	1e9999
#define bool int

real fsqrt(real x)
{
	// assume library doesn't change rounding
	return sqrt(x);
}

#endif

#if	defined(__GNUC__) && defined(__i386__)
#define Platform "LINUX/GNU for Intel"
#include <fpu_control.h>

#define fpclear()	0

void round_down()
{
	__volatile unsigned short int __cw;
	__asm __volatile ("fnstcw %0" : "=m" (__cw));
	__cw = (__cw & 0xf3ff) | _FPU_RC_DOWN;
	__asm __volatile ("fldcw %0" : : "m" (__cw));
}

void round_near()
{
	__volatile unsigned short int __cw;
	__asm __volatile ("fnstcw %0" : "=m" (__cw));
	__cw = (__cw & 0xf3ff) | _FPU_RC_NEAREST;
	__asm __volatile ("fldcw %0" : : "m" (__cw));
}

void round_up()
{
	__volatile unsigned short int __cw;
	__asm __volatile ("fnstcw %0" : "=m" (__cw));
	__cw = (__cw & 0xf3ff) | _FPU_RC_UP;
	__asm __volatile ("fldcw %0" : : "m" (__cw));
}

int status()
{
	__volatile unsigned short int __sw;
	__asm __volatile ("fnstsw %0" : "=m" (__sw));
	return __sw & (_FPU_MASK_IM+_FPU_MASK_ZM+_FPU_MASK_OM+_FPU_MASK_UM);
}

void maskall()
{
	__volatile unsigned short int __cw = _FPU_DEFAULT;
	__asm __volatile ("fldcw %0" : : "m" (__cw));
}

real infinity()
{
	long a = 0x7f800000l;
	return * (float *) &a;
}

real fsqrt(real x)
{
	// assume library doesn't change rounding
	return sqrt(x);
}

#endif

#ifndef Platform
#error Must specify a Platform.
#endif

/****************************************************************************\
A couple of real functions for convenience.

\****************************************************************************/

inline real fmin(real x, real y)
{
	return x < y ? x : y;
}

inline real fmax(real x, real y)
{
	return x < y ? y : x;
}

/****************************************************************************\
Definition of the basic interval type. Each interval is a pair of reals,
and each real is a single or double precision (IEEE 754 4 or 8-byte) floating
point number.
The value (l,r) represents the interval { x : l <= x <= r }.
Most operations assume that l <= r, but an intersection can give l > r,
in which case the interval is the empty set.
\****************************************************************************/

struct realpair;
typedef struct realpair rp;
typedef const struct realpair &crp;

struct realpair
{
	real l, r;	// left, right endpoints
	typedef rp (*func)(rp);

// constructors
	realpair(){}
	realpair(real x) { l = r = x;}
	realpair(real x, real y) { l = x; r = y;}
	realpair operator =(real x) { l = r = x; return *this;}

// obscure internals
	real width() const;	//{ return ((rp) r - l).r;}
	void split(rp &x, rp &y) const;

// arithmetic & set operations
	friend bool operator <=(crp X, crp Y) { return X.r <= Y.l;}
	friend bool operator <(crp X, crp Y) { return X.r < Y.l;}
	friend bool operator >=(crp X, crp Y) { return X.l >= Y.r;}
	friend bool operator >(crp X, crp Y) { return X.l > Y.r;}
	friend bool operator !=(crp X, crp Y) { return X < Y || Y < X;}
	friend rp operator &(crp X, crp Y)	// intersection
		{ return rp(fmax(X.l,Y.l),fmin(X.r,Y.r));}
	friend rp operator |(crp X, crp Y)	// union
		{ return rp(fmin(X.l,Y.l),fmax(X.r,Y.r));}
	friend rp operator &=(rp &X, crp Y) { return X = X & Y;}
	bool isEmpty() const { return l > r;}
	friend bool operator <<=(rp X, rp Y)	// is x contained in y?
		{ return Y.l <= X.l && X.r <= Y.r;}
};

rp Max(rp X, rp Y)
{
	return rp(fmax(X.l,Y.l),fmax(X.r,Y.r));
}

rp Min(rp X, rp Y)
{
	return rp(fmin(X.l,Y.l),fmin(X.r,Y.r));
}

rp operator -(crp X)
{
	rp Y;
	Y.l = - X.r;
	Y.r = - X.l;
	return Y;
}

rp operator +(crp X, crp Y)
{
	rp Z;
	round_down();
	Z.l = X.l + Y.l;
	round_up();
	Z.r = X.r + Y.r;
	round_near();
	return Z;
}

rp operator -(crp X, crp Y)
{
	rp Z;
	round_down();
	Z.l = X.l - Y.r;
	round_up();
	Z.r = X.r - Y.l;
	round_near();
	return Z;
}

void operator +=(rp &X, crp Y)
{
	round_down();
	X.l += Y.l;
	round_up();
	X.r += Y.r;
	round_near();
}

rp operator *(crp X, crp Y)
{
	rp Z;
	round_down();
	if (X.l >= 0)
	{
		Z.l = (Y.l >= 0 ? X.l : X.r) * Y.l;
		round_up();
		Z.r = (Y.r >= 0 ? X.r : X.l) * Y.r;
	}
	else if (Y.l >= 0)
	{
		// can assume X.l < 0
		Z.l = X.l * Y.r;
		round_up();
		Z.r = X.r * (X.r >= 0 ? Y.r : Y.l);
	}
	else if (X.r < 0)
	{
		// can assume Y.l < 0
		Z.l = (Y.r >= 0 ? X.l : X.r) * Y.r;
		round_up();
		Z.r = X.l * Y.l;
	}
	else if (Y.r < 0)
	{
		// can assume X.l < 0, X.r >= 0
		Z.l = Y.l * X.r;
		round_up();
		Z.r = X.l * Y.l;
	}
	else
	{
		// can assume X.l < 0, X.r >= 0, Y.l < 0, Y.r >= 0
		if (X.r == 0)
		{
			if (Y.r == 0) Z.l = 0;
			else Z.l = X.l * Y.r;
			round_up();
			Z.r = X.l * Y.l;
		}
		else
		{
			Z.l = fmin(X.l * Y.r, X.r * Y.l);
			round_up();
			Z.r = fmax(X.l * Y.l, X.r * Y.r);
		}
	}
	round_near();
	return Z;
}

static rp divide(crp X, crp Y)
{
	rp Z;
	assert (Y.l > 0);
	round_down();
	Z.l = X.l / (X.l >= 0 ? Y.r : Y.l);
	round_up();
	Z.r = X.r / (X.r >= 0 ? Y.l : Y.r);
	round_near();
	return Z;
}

rp operator /(crp X, crp Y)
{
	if (Y.l > 0) return divide(X,Y);
	else if (Y.r < 0) return divide(-X,-Y);
	real z = infinity();
	return rp(-z,z);
}

rp operator ^(crp X, int y)
// return x to the power of y
// warning: this operator has low precedence in C
// so you will usually have to parenthesize it
{
	assert (y == 2);
	rp Z;
	if (X.l >= 0)
	{
		round_down();
		Z.l = X.l * X.l;
		round_up();
		Z.r = X.r * X.r;
		round_near();
	}
	else if (X.r <= 0) Z = (-X)^2;
	else
	{
		Z.l = 0;
		round_up();
		Z.r = fmax(X.l*X.l,X.r*X.r);
	}
	return Z;
}

rp Sqrt(rp X)
{
	// assume that X can be narrowed so x >= 0
	if (X.l < 0) X.l = 0;
	if (X.r < 0) X.r = 0;
	rp Y;
	round_down();
	Y.l = fsqrt(X.l);
	round_up();
	Y.r = fsqrt(X.r);
	round_near();
	return Y;
}

const rp Root3 = Sqrt((rp)3);

void rp::split(rp &x, rp &y) const
{
	// split this so it is x | y
	real xm = .5*(l + r);
	x = rp(l,xm);
	y = rp(xm,r);
}

real rp::width() const
{
	return ((rp) r - l).r;
}

/****************************************************************************\
Numerical integration routine, and functions to be integrated. For 
simplicity in passing functions as parameters, some global data is used.

The integration endpoints may overlap, but it is only necessary to
examine  integrals with the first endpoint less than the second.
That is, integrate(F,A,B) should contain every value of the
integral of f from a to b, where a is in A, b is in B, a < b,
and f(x) is in F(X) for each x and X with x in X.

\****************************************************************************/

// data for informative display about the number of compuations performed
static long successes = 0, integcount = 0;
static real minwidth = 1; // keeps track of minimum width of input rectangles
// Allows tracking of maximal number of rectangle divisions

rp Integrate(rp::func F, rp A, rp B)
{
	// bound with upper and lower Riemann sums
	++integcount;
	rp H, R = 0;
	if (B <= A) return 0;
	H = (rp)(B.l - A.r) / 32;
	if (H.r > 0)
	for (int i = 0; i < 32; ++i)
	{
		R += (*F)(A.r + i*H + (0 | H));
	}
	rp r = (0|(*F)(A))*A.width() + (0|(*F)(B))*B.width() + R * H;
	printf("(%.8f,%.8f) (%.8f,%.8f) -> (%.8f,%.8f)\n", A.l + 0., A.r, B.l + 0., B.r, r.l + 0., r.r);
  return r;
}

struct globals
{
	// this global data is used by functions to be integrated
	rp H, Force, Y_min, Y_max;
} Global;

static void setGlobal(rp H, rp Force)
// assign globals for subsequent integration
{
	Global.H = H;
	Global.Force = Force;
}

static rp Dx(rp X)
{
	rp T = Global.H*(X^2) - Global.Force;
	return T / Sqrt((2*X + T)*(2*X - T));
}

static rp Dxmin(rp Z)
{
	rp Y = Global.Y_min + (Z^2);
	rp T = Global.H*(Y^2) - Global.Force;
	return 2 * T
		/ Sqrt((2*Y + T)*(2 - Global.H * Global.Y_min - Y*Global.H));
}

static rp Dxmax(rp Z)
{
	rp Y = Global.Y_max - (Z^2);
	rp T = Global.H*(Y^2) - Global.Force;
	rp Y_min = Global.Force / (1 + Sqrt(1 + Global.Force*Global.H));
	return 2 * T / Sqrt((2*Y + T)*Global.H*(Y + Y_min));
}

static rp Dv(rp X)
// volume integrand, singularity at Global.Y_min, Global.Y_max
// omits factor of pi
{
	return (X^2) * Dx(X);
}

static rp Dvmin(rp Z)
// volume integrand, singularity at Global.Y_min resolved
// omits factor of pi
{
	rp Y = Global.Y_min + (Z^2);
	return (Y^2) * Dxmin(Z);
}

static rp Dvmax(rp Z)
// volume integrand, singularity at Global.Y_max resolved
// omits factor of pi
{
	rp Y = Global.Y_max - (Z^2);
	return (Y^2) * Dxmax(Z);
}

/****************************************************************************\
main rejection routines


\****************************************************************************/

real avgwt(rp X, rp Y, real wt)
// returns a point between x and y.  Rounding is not material here.
{
	assert (X < Y);
	return (1-wt)*X.r + wt*Y.l;
}

rp Compare(rp X, rp Y, rp A, rp B)
//  interval version of x < y ? a : b
{
	if (X < Y) return A;
	else if (X > Y) return B;
	else return A | B; // returns union if intervals X,Y overlap
}

static int reject(rp c1, rp h0, int n)
{
  printf("reject at step %d\n", n);
  return n;
}

// Rejection codes.
// Values can be used to analyze why torus bubbles are rejected.
#define NORESULT 0
#define REJECT(n) reject(C_1, H_o, n)

int CheckRectangle(rp C_1, rp H_o)
// return a positive exclusion code if successful
{
  printf("(%.8f,%.8f)\n", C_1.l + 0., C_1.r);
  printf("(%.8f,%.8f)\n", H_o.l + 0., H_o.r);
// step 1
	// check based on Proposition 4.21.
  if (1000*C_1 >= 996 && 5*H_o <= 1) {
    /*
    printf("reject at step 1\n");
	printf("(%.8f,%.8f)\n", C_1.l + 0., C_1.r);
	printf("(%.8f,%.8f)\n", H_o.l + 0., H_o.r);
    */
	return REJECT(1);
  }

// step 2
	rp H_i = 2 - H_o;
	rp Y_1 = Sqrt(1 - (C_1^2));
	rp F_i = (H_i - 1)*(Y_1^2) - C_1*Y_1*Root3;
	rp F_o = - F_i;
	rp C_2 = (-C_1 | C_1) & rp(-.5,.5);
	if (C_2.isEmpty()) return REJECT(2);
	rp Ht = H_i - 1;
	rp T = (2*Ht*F_i + 3) / (3 + (Ht^2)) - (1 - (C_1^2));
	/*
	printf("value of t:\n");
	printf("(%.8f,%.8f)\n", T.l + 0., T.r);
	printf("at step 2 on c1,h0 : \n");
	printf("(%.8f,%.8f)\n", C_1.l + 0., C_1.r);
	printf("(%.8f,%.8f)\n", H_o.l + 0., H_o.r);
	*/
	if ((C_2^2) + T != 1) {
	  //printf("rejected\n");
	  return REJECT(2);
	}

// step 3
	rp Y_2 = Sqrt(T & rp(0,1));
	if (!(Y_2 > 0)) return NORESULT;
	assert (Y_2 > 0);
	C_2 &= (Ht*Y_2 - F_i/Y_2) / Root3;
	if (C_2.isEmpty()) return REJECT(3);	// never happens

// step 4
	// compare to standard double bubble
	if (C_1 <= .5 && Y_1 > 0 && H_o < 1 - Root3 * C_1 / Y_1)
		return REJECT(4);

// step 5
	// if the endpoint is too fat, go back and subdivide input
	if (C_2.width() > .5) return NORESULT;

// step 6
	// set Global.Y_min,Global.Y_max for use by integration routines
	Global.Y_min = - F_i / (1 + Sqrt(1 + F_i*H_i));	// local y min
	Global.Y_max = (1 + Sqrt(1 + F_o*H_o)) / H_o;		// local y max
	rp W_ends = ((1-C_1)^2)*(2+C_1)/3 + ((1-C_2)^2)*(2+C_2)/3;
	rp Y = Compare(C_1,Root3/2,Global.Y_min,Y_1);
	if (Y * H_i < -1 && Y > 0)
	{
		// test for inefficient torus
		rp R = (Root3 / 2) / (-H_i - 1/Y);
		rp W = 2.5 * (R^2) * (Y + R*Root3/2);	// upper bd for vol/pi
		if (W < W_ends) return REJECT(6);
	}

// step 7
	// calc some integration endpoints
	rp Y_left = Sqrt(F_o/H_o);
	if (Global.Y_min < Y_2 && Y_left < Global.Y_max)
		Y_left = Max(Y_1,Y_left);
	else return NORESULT;		// need more accuracy
	rp Y_4 = avgwt(Y_left,Global.Y_max,1/16.);
	rp Z_2 = Sqrt(Global.Y_max-Y_2);
	rp Z_4 = - Sqrt(Global.Y_max-Y_4);
	rp Delta_i, Delta_o;
	rp yymin = Global.Y_max - 2/H_o;
	if (1000*C_1 >= 998)
	{
		T = avgwt(Y_1,Y_2,.5);
		Delta_i = (T - Y_1) * 33/16.;
		setGlobal(H_i,F_i);		// set globals for integration
		Delta_i += Integrate(Dx,T,Y_2);
		Delta_o = - (Y_left - Y_1) * Root3;
		T = avgwt(Y_left,Y_4,1/16.);
		setGlobal(H_o,F_o);
		Delta_o += Integrate(Dx,T,Y_4);
		if (Delta_i < Delta_o) return REJECT(7);
		Delta_o += Integrate(Dxmax,Z_4,Z_2);
		if (Delta_i < Delta_o) return REJECT(7);
		if (1 <<= C_1) return NORESULT;
	}

// step 8
	// calc inner curve width
	assert (C_1 <= Root3/2 || Y_1 <= Y_2);
	T = Sqrt(Y_1-Global.Y_min);
	rp Z_1 = Compare(C_1,Root3/2,-T,T);
	rp Z_3 = Sqrt(Y_2-Global.Y_min);
	setGlobal(H_i,F_i);
	Delta_i = Integrate(Dxmin,Z_1,Z_3);
	// calc outer curve width
	setGlobal(H_o,F_o);
	Delta_o = Integrate(Dxmax,Z_4,Z_2);
	if (Delta_i < Delta_o) return REJECT(8);
	printf("h0 is\n");
	printf("(%.8f,%.8f)\n", H_o.l + 0., H_o.r);
	printf("f0 is\n");
	printf("(%.8f,%.8f)\n", F_o.l + 0., F_o.r);
	printf("t is\n");
	printf("(%.8f,%.8f)\n", T.l + 0., T.r);
	Delta_o += Integrate(Dx,Y_1,Y_4);
	if (Delta_i != Delta_o) return REJECT(8);

// can prove with return here, but very slow
//	return NORESULT;

// step 9
	// calc inner curve volume
	setGlobal(H_i,F_i);
	rp W_base = Integrate(Dvmin,Z_1,Z_3);
	rp W_i = W_base + W_ends;
	// calc outer curve volume
	setGlobal(H_o,F_o);
	rp foo = Integrate(Dv,Y_1,Y_4);
	rp W_o = foo + Integrate(Dvmax,Z_4,Z_2) - W_base;
	if (W_i != W_o) return REJECT(9);
	return NORESULT;
}

int DivideAndCheckRectangle(rp Y_1, rp H_o)
// return -1 on failure
{
	if (Y_1.width() < minwidth) minwidth = Y_1.width();
	rp C_1 = Sqrt(1 - (Y_1^2));
	assert (C_1 <= 1);
	int i = CheckRectangle(C_1,H_o);
	if (i)
	{
		if (i < 0) return -1;
		++successes;
		return 1 << i;
	}
	assert (Y_1.width() > .001 && H_o.width() > .01);
	rp Ya, Yb, Ha, Hb;
	Y_1.split(Ya,Yb);
	H_o.split(Ha,Hb);
	i |= DivideAndCheckRectangle(Ya,Ha);
	if (i < 0) return i;
	i |= DivideAndCheckRectangle(Ya,Hb);
	if (i < 0) return i;
	i |= DivideAndCheckRectangle(Yb,Ha);
	if (i < 0) return i;
	i |= DivideAndCheckRectangle(Yb,Hb);
	if (i < 0) return i;
	return i;
}

/****************************************************************************\
stuff for DOS/UNIX command-line versions
\****************************************************************************/

const char help[] =
	"Program to search for torus bubble counterexamples.\n"
	"See info at http://www.ucdavis.edu/~hass/bubbles.html\n"
	"Usage: doubbub all\n"
	"Program takes 8 to 60 seconds on typical 1999 computers.\n";

int main(int argc, char *argv[])
{
	if (argc <= 1)
	{
		printf(help);
		return 0;
	}
	if (argv[1][0] != 'a')
	{
		printf("Unknown option\n");
		return 1;
	}
	time_t t = time(0);
	printf("Platform = %s\n",Platform);
	maskall();

	// first some simple checks
	assert (sizeof(rp) == 8 || sizeof(rp) == 16);
	assert (Root3.width() > 0);
	assert (Root3.width() < 1e-6);
	rp X = Root3^2;
	assert (X.l < 3 && 3 < X.r);
	X = infinity();
	assert (X > 1e37);

	// the main calculation
	rp Y_1 = rp(0,1);
	rp H_o = rp(0,10);
	if (DivideAndCheckRectangle(Y_1,H_o) < 0)
	{
		printf("Torus bubble calculation failed.\n");
		exit(1);
	}
	int final = status();
	if (final) printf("Warning: floating point exception occurred,"
		" status = %.4X\n",final);
	t = time(0) - t;
	printf("Finished calculations, successes = %ld, integrals = %ld, "
		"dY = %.5f\n",successes,integcount,minwidth);
	printf("All torus bubbles rejected. Elapsed time: %ld sec.\n",t);
	if (successes != 15016l || integcount != 51256l || 1024*minwidth != 1)
		printf("WARNING: totals do not match published figures\n");
	return 0;
}
