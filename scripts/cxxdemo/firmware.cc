#include <stdio.h>
#include <iostream>
#include <vector>
#include <algorithm>

int main()
{
	printf("Hello World, C!\n");

	std::cout << "Hello World, C++!" << std::endl;

	std::vector<unsigned int> some_ints;
	some_ints.push_back(0x48c9b3e4);
	some_ints.push_back(0x79109b6a);
	some_ints.push_back(0x16155039);
	some_ints.push_back(0xa3635c9a);
	some_ints.push_back(0x8d2f4702);
	some_ints.push_back(0x38d232ae);
	some_ints.push_back(0x93924a17);
	some_ints.push_back(0x62b895cc);
	some_ints.push_back(0x6130d459);
	some_ints.push_back(0x837c8b44);
	some_ints.push_back(0x3d59b4fe);
	some_ints.push_back(0x444914d8);
	some_ints.push_back(0x3a3dc660);
	some_ints.push_back(0xe5a121ef);
	some_ints.push_back(0xff00866d);
	some_ints.push_back(0xb843b879);

	std::sort(some_ints.begin(), some_ints.end());

	for (auto n : some_ints)
		std::cout << std::hex << n << std::endl;

	std::cout << "All done." << std::endl;
	return 0;
}
