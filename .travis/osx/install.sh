#!/bin/bash

# Enable debugging and logging of shell operations
# that are executed.
set -e
set -x

# Install requirements of MAC OS X
brew update
brew install md5sha1sum bison libtool mcpp libffi
brew link bison --force
brew link libffi --force

export PATH="/usr/local/opt/bison/bin:$PATH"
export PKG_CONFIG_PATH=/usr/local/opt/libffi/lib/pkgconfig/

rm /Users/travis/Library/Logs/DiagnosticReports/* || true
