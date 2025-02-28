// RUN: %clang_cc1 -triple %itanium_abi_triple -emit-llvm %s -o - | FileCheck %s
struct A { char s, t, u, v; short a; };
// CHECK: %a = alloca %struct.A, align 2
// CHECK: %b = alloca %struct.A, align 2
// CHECK: call void @llvm.memcpy.p0.p0.{{.*}} align 2 {{.*}} align 2 {{.*}}, i1 false)

void q(void) { struct A a, b; a = b; }
