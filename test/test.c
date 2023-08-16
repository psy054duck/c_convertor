#include <stdbool.h>
extern int unknown1(void);
extern int unknown2(void);
extern void assert(bool);

int main()
{
	int x = 0;
	int y = 0;
	int z = 0;
	int v = 0;
	// x = x + 1;
	// x = x + 1;
	// x = x + 1;
	// x = x + 1;
	// x = x + 1;
	// if (x < 0) {
	// 	y++;
	// 	z++;
	// 	v++;
	// } else {
	// 	y--;
	// 	z--;
	// 	v--;
	// }
	for (int i = 0; i < 100; i++) {
		// for (int j = 0; j < 100; j++) {
			x++;
		// }
	}
	assert(x == 100);
	assert(y == 0);
	assert(z == -1);
	// assert(x + y == 100);
	// unsigned int x = 0;
	// unsigned int y = 10;
	// unsigned int z=5000000;
	// while(x<z){	
	// 	x += 2;
	// 	y += 5;
	// }
	// // assert(x == z);
	// assert(y % 5 == 0);
	// return 0;
}