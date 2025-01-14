// RUN: %clang_cc1 -triple %itanium_abi_triple -fno-builtin-memccpy -emit-llvm < %s| FileCheck %s

typedef __SIZE_TYPE__ size_t;

void *memccpy(void *, void const *, int, size_t);

void test13(char *d, char *s, int c, size_t n) {
  // CHECK: call ptr @memccpy{{.*}} #2
  memccpy(d, s, c, n);
}

// CHECK: attributes #2 = { nobuiltin "no-builtin-memccpy" }
