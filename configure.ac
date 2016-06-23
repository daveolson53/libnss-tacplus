dnl
dnl File:        configure.in
dnl Revision:    $Id: configure.ac,v 1.0 2014/11/03 12:04:29 olson Exp $
dnl Created:     2014/11/02
dnl Author:      Dave Olson <olson@cumulusnetworks.com>
dnl
dnl Process this file with autoconf to produce a configure script
dnl You need autoconf 2.59 or better!
dnl
dnl ---------------------------------------------------------------------------

AC_PREREQ(2.59)
AC_COPYRIGHT([
See the included file: COPYING for copyright information.
])
AC_INIT(libnss_tacplus, 2.0.0, [olson@cumulusnetworks.com])
AC_CONFIG_AUX_DIR(config)
AM_INIT_AUTOMAKE
AC_CONFIG_SRCDIR([nss_tacplus.c])
AC_CONFIG_HEADER([config.h])
AC_CONFIG_MACRO_DIR([config])

# no static lib version
LT_INIT([disable-static])

AC_ENABLE_SHARED(yes)
AC_ENABLE_STATIC(no)

dnl --------------------------------------------------------------------
dnl Checks for programs.
AC_PROG_CC
AM_PROG_CC_C_O
AC_PROG_INSTALL
AC_PROG_LN_S
AC_PROG_MAKE_SET
AM_PROG_LIBTOOL

# Add -Wall -Werror if we are using GCC.
if test "x$GCC" = "xyes"; then
      CFLAGS="$CFLAGS -Wall -Werror"
fi

dnl --------------------------------------------------------------------
dnl Checks for libraries.
AC_CHECK_LIB(tac, tac_connect)

case "$host" in
	sparc-* | sparc64-*)
		LIBS="$LIBS -lresolv";;
esac

dnl --------------------------------------------------------------------
dnl Checks for header files.
AC_HEADER_STDC
AC_CHECK_HEADERS([nss.h fcntl.h stdlib.h string.h strings.h sys/socket.h sys/time.h syslog.h unistd.h])
AC_CHECK_HEADERS([tacplus/libtac.h])

dnl --------------------------------------------------------------------
dnl Checks for typedefs, structures, and compiler characteristics.
AC_C_CONST
AC_TYPE_SIZE_T
AC_HEADER_TIME

dnl --------------------------------------------------------------------
dnl Checks for library functions.
AC_FUNC_REALLOC
AC_FUNC_SELECT_ARGTYPES
AC_TYPE_SIGNAL
AC_CHECK_FUNCS([gethostbyname gettimeofday inet_ntoa select socket])

dnl --------------------------------------------------------------------
dnl Generate made files
AC_CONFIG_FILES([Makefile])
AC_OUTPUT
