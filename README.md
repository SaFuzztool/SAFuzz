# SAFuzz
This is the repo of **Multiple Targets Directed Greybox Fuzzing: From Reachable to Exploited**.

## How to build
```bash
# build fuzzer
cd fuzz
make clean all
cd llvm_mode
make clean all

# build instrumentor (need llvm10_obj)
export LLVM_DIR=/your/build/llvm10/obj
cd instrument
cmake . -DSVF_DIR=../SVF/
make
```

## How to use
```bash
export SUBJECT=$PWD
git clone https://github.com/libming/libming.git libming-CVE-2018-8807
cd libming-CVE-2018-8807
git checkout b72cc2f
./autogen.sh
mkdir build; 
cd build
CC=$SUBJECT/gllvm/gclang CXX=$SUBJECT/gllvm/gclang++ ../configure --disable-shared
make clean; make
cd util; $SUBJECT/gllvm/get-bc swftophp
cd ../
mkdir fuzz; cd fuzz
cp ../util/swftophp.bc .
echo $'decompile.c:398' > targets
$SUBJECT/instrument/cbi --targets=targets swftophp.bc
$SUBJECT/fuzz/afl-clang-fast swftophp.ci.bc -lpng16 -lm -lz -lfreetype -o swftophp.ci
mkdir in; wget -P in http://condor.depaul.edu/sjost/hci430/flash-examples/swf/bumble-bee1.swf
AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1 AFL_SKIP_CPUFREQ=1 $SUBJECT/fuzz/afl-fuzz -d -i in/ -o out ./swftophp.ci @@
```


