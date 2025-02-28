// UNSUPPORTED: -zos, -aix
// Test for rdar://10278815

// Without PCH
// RUN: %clang_cc1 -triple %itanium_abi_triple -fsyntax-only -verify -include %s %s

// With PCH
// RUN: %clang_cc1 -triple %itanium_abi_triple %s -emit-pch -o %t
// RUN: %clang_cc1 -triple %itanium_abi_triple -emit-llvm-only -verify %s -include-pch %t -debug-info-kind=limited

// expected-no-diagnostics

#ifndef HEADER
#define HEADER
//===----------------------------------------------------------------------===//
// Header

typedef char BOOL;

@interface NSString
+ (BOOL)meth;
@end

static NSString * const cake = @"cake";

//===----------------------------------------------------------------------===//
#else
//===----------------------------------------------------------------------===//

@interface Foo {
  BOOL ivar;
}
@end

//===----------------------------------------------------------------------===//
#endif
