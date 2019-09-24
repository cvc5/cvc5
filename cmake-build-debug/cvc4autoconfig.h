#ifndef __CVC4__CVC4AUTOCONFIG_H
#define __CVC4__CVC4AUTOCONFIG_H

/* Major component of the version of CVC4. */
#define CVC4_MAJOR 1

/* Minor component of the version of CVC4. */
#define CVC4_MINOR 8

/* Release component of the version of CVC4. */
#define CVC4_RELEASE 0

/* Extraversion component of the version of CVC4. */
#define CVC4_EXTRAVERSION "-prerelease"

/* Full release string for CVC4. */
#define CVC4_RELEASE_STRING "1.8-prerelease"

/* Full name of this package. */
#define CVC4_PACKAGE_NAME "cvc4"

/* Define to 1 if CVC4 is built with (optional) GPLed library dependencies. */
#define CVC4_GPL_DEPS 0

/* Define to use the CLN multi-precision arithmetic library. */
/* #undef CVC4_CLN_IMP */

/* Define to use the GMP multi-precision arithmetic library. */
#define CVC4_GMP_IMP

/* Define to 1 if Boost threading library has support for thread attributes. */
#define BOOST_HAS_THREAD_ATTR 0

/* Define if `clock_gettime' is supported by the platform. */
#define HAVE_CLOCK_GETTIME

/* Define to 1 if the declaration of `optreset' is available. */
#define HAVE_DECL_OPTRESET 1

/* Define to 1 if the <ext/stdio_filebuf.h> header file is available. */
#define HAVE_EXT_STDIO_FILEBUF_H 0

/* Define if `ffs' is supported by the platform. */
#define HAVE_FFS

/* Define to 1 to use libreadline. */
#define HAVE_LIBREADLINE 0

/* Define if `sigaltstack' is supported by the platform. */
#define HAVE_SIGALTSTACK

/* Define to 1 if `strerror_r' is supported by the platform. */
#define HAVE_STRERROR_R 1

/* Define if `strtok_r' is supported by the platform. */
#define HAVE_STRTOK_R

/* Define to 1 if the <unistd.h> header file is available. */
#define HAVE_UNISTD_H 1

/* Define to 1 if `rl_completion_entry_function' returns (char *). */
#define READLINE_COMPENTRY_FUNC_RETURNS_CHARP 0

/* Define to 1 if `strerror_r' returns (char *). */
#define STRERROR_R_CHAR_P 0

#endif /* __CVC4__CVC4AUTOCONFIG_H */
