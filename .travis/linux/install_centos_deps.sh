#!/bin/sh

yum install -y https://dl.bintray.com/souffle-lang/rpm-unstable/centos/7/x86_64/souffle-repo-centos-1.0-1.x86_64.rpm

yum install -y autoconf automake bison clang doxygen flex gcc gcc-c++ git kernel-devel ncurses-devel sqlite-devel libtool make mcpp python sqlite sudo zlib-devel

yum install -y ruby-devel gcc make rpm-build libffi-devel

gem install --no-ri --no-rdoc fpm

fpm --version
