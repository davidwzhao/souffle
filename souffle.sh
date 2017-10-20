#!/bin/bash

# comments with more than one '#' are displayed in the help text
##
## > souffle.sh
##
## A quick and dirty bash script for developing souffle.
##
## Usage:

# add environment variable '$SOUFFLE' for souffle executable
export SOUFFLE=$(pwd)

# add aliases 'souffle' and 'souffle-profile'
alias souffle=$SOUFFLE/src/souffle
alias souffle-profile=$SOUFFLE/src/souffle-profile

case $1 in
    ## - apt-get: Install package dependencies for systems using apt-get.
    apt-get)
        # install package dependencies
        sudo apt-get update -y;
        sudo apt-get install -y $(
			echo $( \
				cat README.md | \
				grep "apt-get install" | \
				sed 's/^.*apt-get install//g' \
			) \
        );
        sudo apt-get install -y clang-4.0 clang-format-4.0 libomp-dev;
    ;;
    ## - sync: Sync upstream and origin master, and format with clang.
    sync)
        # - format with clang
        clang-format-4.0 \
            -i \
            -style=file \
            $SOUFFLE/src/*.cpp \
            $SOUFFLE/src/*.h \
            $SOUFFLE/src/test/*.cpp \
            $SOUFFLE/src/test/*.h &&
            # ensure imported library files and permissions are intact
            git checkout upstream/master -- src/mcpp*.[chCH];
            chmod 775 bootstrap .travis/* debian/rules osx/preinstall;
            # add and commit with git
            git add .;
            git commit -m "$(date)";
            # fetch all from upstream and origin
            git fetch origin;
            git fetch origin --tags;
            git fetch upstream;
            git fetch upstream --tags;
            # pull upstream and origin master to current branch
            git pull upstream master;
    ;;
    ## - build: Build Souffle from scratch.
    build)
		make clean;
		case $2 in
			clang)
				export CC=clang-4.0;
				export CXX=clang++-4.0;
			;;
			gcc)
				export CC=gcc;
				export CXX=g++;
			;;
			*)
			;;
		esac;
        # run boostrap and configure
        chmod 775 bootstrap && \
        ./bootstrap && \
        chmod 775 configure && \
        ./configure --enable-debug && \
        # run make
        make -j8;
    ;;
    ## - debug <group>/<test> <options>: Debug a given <group>/<test> on <options> from the testsuite.
    debug)
        shift
        id=$(echo "${@}" | grep "\-[a-z]" -o | sort | sed 's/-//');
        in_path=${PWD}/tests/$1
        out_path=${PWD}/tests/testsuite.dir/$1/id
        shift
        cmd=$1
        shift
        args="${@}"
        case ${cmd} in
            valgrind)
                cmd="valgrind"
            ;;
            *)
                args="${cmd} ${args}"
                cmd=""
            ;;
        esac;
        [[ ! -e ${in_path} ]] && echo "Error!" && exit 1
        rm -rf ${out_path}
        mkdir -p ${out_path}
        ${cmd} \
            ${PWD}/src/souffle \
            -F${in_path}/facts \
            -D${out_path} \
            -r${out_path}/`basename ${in_path}`.html \
            ${in_path}/`basename ${in_path}`.dl \
            ${args};
    ;;
    ## - test: Run testsuite under multiple configurations.
    test)
        for cc in clang gcc; do
            ccdir=./tests/testsuite.dir/${cc}
            mkdir -p ${ccdir};
            git clone . ${ccdir};
            xterm -e "cd ${ccdir}; ./souffle.sh build ${cc} && make check -j2; cd -;" & \
            echo "Running for ${cc}..";
        done;
    ;;
    ## - help: Display the help text.
    *)
        cat $0 | grep '##' | grep -v "grep" | sed 's/#//g'
    ;;
esac;
##
