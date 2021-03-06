int source();
void sink(...) {};

void arithAssignments(int source1, int clean1) {
  sink(clean1); // clean
  clean1 += source1;
  clean1 += 1;
  sink(clean1); // tainted

  clean1 = source1 = 1;
  sink(clean1); // clean
  source1 = clean1 = source();
  source1++;
  ++source1;
  source1 += 1;
  sink(source1); // tainted
  sink(++source1); // tainted
}

// --- globals ---

int increment(int x) {return x + 1;}
int zero(int x) {return 0;}

int global1 = 0;
int global2 = source();
int global3 = global2 + 1;
int global4 = increment(source());
int global5 = zero(source());
int global6, global7, global8, global9, global10;

void do_source()
{
	global6 = 0;
	global7 = source();
	global8 = global7 + 1;
	global9 = increment(source());
	global10 = zero(source());

	sink(global6);
	sink(global7); // tainted
	sink(global8); // tainted
	sink(global9); // tainted
	sink(global10);
}

void do_sink()
{
	sink(global1);
	sink(global2); // tainted [NOT DETECTED]
	sink(global3); // tainted [NOT DETECTED]
	sink(global4); // tainted [NOT DETECTED]
	sink(global5);
	sink(global6);
	sink(global7); // tainted [NOT DETECTED]
	sink(global8); // tainted [NOT DETECTED]
	sink(global9); // tainted [NOT DETECTED]
	sink(global10);
}

void global_test()
{
	do_source();
	do_sink();
}

// --- class fields ---

class MyClass {
public:
	MyClass() : a(0), b(source()) {
		c = source();
		d = 0;
	}

	void myMethod() {
		d = source();
	}

	int a, b, c, d;
};

void class_field_test() {
	MyClass mc1, mc2;

	mc1.myMethod();

	sink(mc1.a);
	sink(mc1.b); // tainted [NOT DETECTED with IR]
	sink(mc1.c); // tainted [NOT DETECTED with IR]
	sink(mc1.d); // tainted [NOT DETECTED with IR]
	sink(mc2.a);
	sink(mc2.b); // tainted [NOT DETECTED with IR]
	sink(mc2.c); // tainted [NOT DETECTED with IR]
	sink(mc2.d);
}

// --- arrays ---

void array_test(int i) {
	int arr1[10] = {0};
	int arr2[10] = {0};
	int arr3[10] = {0};

	arr1[5] = source();
	arr2[i] = source();
	arr3[5] = 0;

	sink(arr1[5]); // tainted
	sink(arr1[i]); // tainted [NOT DETECTED]
	sink(arr2[5]); // tainted [NOT DETECTED]
	sink(arr2[i]); // tainted [NOT DETECTED]
	sink(arr3[5]);
	sink(arr3[i]);
}

// --- pointers ---

void pointer_test() {
	int t1 = source();
	int t2 = 1;
	int t3 = 1;
	int *p1 = &t1;
	int *p2 = &t2;
	int *p3 = &t3;

	*p2 = source();

	sink(*p1); // tainted
	sink(*p2); // tainted [NOT DETECTED]
	sink(*p3);

	p3 = &t1;
	sink(*p3); // tainted

	*p3 = 0;
	sink(*p3); // [FALSE POSITIVE]
}

// --- return values ---

int select(int i, int a, int b) {
	if (i == 1) {
		return a;
	} else {
		return b;
	}
}

void fn_test(int i) {
	sink(select(i, 1, source())); // tainted
}

// --- strings ---

char *strcpy(char *destination, const char *source);
char *strcat(char *destination, const char *source);

namespace strings
{
	char *source(); // char* source

	void strings_test1() {
		char *tainted = source();
		char buffer[1024] = {0};

		sink(source()); // tainted
		sink(tainted); // tainted

		strcpy(buffer, "Hello, ");
		sink(buffer);
		strcat(buffer, tainted);
		sink(buffer); // tainted
	}
}

// --- pass by reference ---

namespace refs {
	void callee(int *p) {
		sink(*p); // tainted
	}

	void caller() {
		int x = source();
		callee(&x);
	}
}

void *memcpy(void *dest, void *src, int len);

void test_memcpy(int *source) {
	int x;
	memcpy(&x, source, sizeof(int));
	sink(x);
}

// --- swap ---

namespace std {
	template<class T> constexpr void swap(T& a, T& b);
}

void test_swap() {
	int x, y;

	x = source();
	y = 0;

	sink(x); // tainted
	sink(y); // clean

	std::swap(x, y);

	sink(x); // clean [FALSE POSITIVE]
	sink(y); // tainted
}

// --- lambdas ---

void test_lambdas()
{
	int t = source();
	int u = 0;
	int v = 0;
	int w = 0;

	auto a = [t, u]() -> int {
		sink(t); // tainted
		sink(u); // clean
		return t;
	};
	sink(a()); // tainted

	auto b = [&] {
		sink(t); // tainted
		sink(u); // clean
		v = source(); // (v is reference captured)
	};
	b();
	sink(v); // tainted [NOT DETECTED]

	auto c = [=] {
		sink(t); // tainted
		sink(u); // clean
	};
	c();

	auto d = [](int a, int b) {
		sink(a); // tainted
		sink(b); // clean
	};
	d(t, u);

	auto e = [](int &a, int &b, int &c) {
		sink(a); // tainted
		sink(b); // clean
		c = source();
	};
	e(t, u, w);
	sink(w); // tainted [NOT DETECTED]
}
