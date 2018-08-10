#!/bin/sh

yum install -y autoconf automake bison clang doxygen flex gcc gcc-c++ git kernel-devel ncurses-devel sqlite-devel libtool make mcpp pkg-config python sqlite sudo zlib-devel

yum install -y ruby-devel gcc make rpm-build libffi-devel

gem install --no-ri --no-rdoc fpm

fpm --version
