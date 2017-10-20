#!/bin/bash

# Enable debugging and logging of shell operations
# that are executed.
set -e
set -x

# Install libomp
sudo add-apt-repository -y "deb http://ftp.us.debian.org/debian unstable main contrib non-free"
sudo apt-get -qq update
sudo apt-get -y --force-yes install libomp-dev


# While we are using a sudo-enabled build, let's also enable coredumps
sudo bash -c "echo 'core' > /proc/sys/kernel/core_pattern"
