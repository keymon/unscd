This is a drop-in replacement for glibc nscd which is designed
for simplicity and stability.  It should be command line and
config compatible.

See the nscd documentation for usage information.

Build instructions:

gcc -Os -o nscd nscd.c

For more info please see comments in nscd.c
