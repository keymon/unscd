#include <stdio.h>
#include <sys/types.h>
#include <pwd.h>
int main(int argc, char **argv)
{
	void *res = getpwnam(argv[1]);
	printf(res ? "Found\n" : "Not found\n");
	return res == 0;
}

