###########################################################################
##
## Copyright 2014, 2015, 2016 Cumulus Networks.  All rights reserved.
## Author: Dave Olson <olson@cumulusnetworks.com>
##
###########################################################################

ACLOCAL_AMFLAGS = -I config

moduledir = @libdir@
module_LTLIBRARIES = libnss_tacplus.la

# we don't want our header installed, so just list it in SOURCES.

libnss_tacplus_la_SOURCES = \
nss_tacplus.c \
nss_tacplus.h

libnss_tacplus_la_CFLAGS = $(AM_CFLAGS)
# Version 2.0 because that's the NSS module version, and they must match
libnss_tacplus_la_LDFLAGS = -module -version-info 2:0:0 -shared
libnss_tacplus_la_LIBADD = -ltacplus_map -ltac -laudit


EXTRA_DIST = tacplus_nss.conf README ChangeLog

MAINTAINERCLEANFILES = Makefile.in config.h.in configure aclocal.m4 \
                       config/config.guess  config/config.sub  config/depcomp \
                       config/install-sh config/ltmain.sh config/missing

clean-generic:
	rm -rf autom4te*.cache 
	rm -f *.rej *.orig *.lang

MULTI_OS_DIRECTORY=$(shell $(CC) $(CFLAGS) -print-multiarch)
# This and the install rules using it are copied from libnss-ldap-264
LIBC_VERS = $(shell ls /lib/$(MULTI_OS_DIRECTORY)/libc-*.so | sed -e '1s|.*libc-\(.*\)\.so|\1|')
NSS_TACPLUS_LIBC_VERSIONED = libnss_tacplus-$(LIBC_VERS).so

NSS_VERS = $(shell ls /lib/$(MULTI_OS_DIRECTORY)/libnss_files.so.? | sed -e '1s|.*libnss_files\.so\.\(.*\)|\1|')
NSS_TACPLUS_NSS_VERSIONED = libnss_tacplus.so.$(NSS_VERS)

# strip all but the NSS entry point, to avoid symbol pollution
# nobody will link against this plugin, so no need for .la
# for NSS, we don't need to install the libnss_tacplus.so.2.0.0
# and don't want libnss_tacplus.so either since the library is a plugin.
# libtool installs both automatically, so we remove them.
# Copying debian and installing main copy as file with libc version,
# and the .so.2 version as a symlink to the libc versioned file
install-data-hook:
	rm -f $(DESTDIR)$(libdir)/libnss_tacplus.la
	rm -f $(DESTDIR)$(libdir)/libnss_tacplus.so $(DESTDIR)$(libdir)/libnss_tacplus.so.2.0.0
	$(mkinstalldirs) $(DESTDIR)$(libdir) $(DESTDIR)$(sysconfdir)
	cd .libs && $(INSTALL_PROGRAM) libnss_tacplus.so $(DESTDIR)$(libdir)/$(NSS_TACPLUS_LIBC_VERSIONED)
	$(STRIP) --keep-symbol=_nss_tacplus_getpwnam_r --keep-symbol=_nss_tacplus_getpwuid_r $(DESTDIR)$(libdir)/$(NSS_TACPLUS_LIBC_VERSIONED)
	cd $(DESTDIR)$(libdir); ln -sf $(NSS_TACPLUS_LIBC_VERSIONED) $(NSS_TACPLUS_NSS_VERSIONED)
	${INSTALL} -m 644 tacplus_nss.conf $(DESTDIR)$(sysconfdir)

