// RUN: %clang_cc1 -triple %itanium_abi_triple -emit-llvm -o - %s | FileCheck %s

@interface Test
- (void)test;
@end

@implementation Test
- (void)test __attribute__((minsize)) {
    // CHECK: define{{.*}}Test test
    // CHECK: minsize
}
@end
