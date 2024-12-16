; NOTE: Assertions have been autogenerated by utils/update_test_checks.py UTC_ARGS: --version 2
; RUN: opt -load-pass-plugin ../../tasks/dead-code-elimination/build/libDeadCodeElimination.%SHLIBEXT% -passes=dead-code-elimination -S < %s | FileCheck %s

; ModuleID = 'example-1.ll'
source_filename = "simple-1.ll"
target triple = "x86_64-unknown-linux-gnu"

define dso_local i32 @main(i32 %argc, ptr %argv) {
; CHECK-LABEL: define dso_local i32 @main
; CHECK-SAME: (i32 [[ARGC:%.*]], ptr [[ARGV:%.*]]) {
; CHECK-NEXT:  entry:
; CHECK-NEXT:    ret i32 0
;
entry:
  %add = add nsw i32 %argc, 42
  %mul = mul nsw i32 %add, 2
  ret i32 0
}