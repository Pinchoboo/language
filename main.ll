; ModuleID = './out/main.ll'
source_filename = "module"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%const_map_int_to_char = type { i64, i64*, i8* }

@g.keys = internal global [5 x i64] [i64 0, i64 1, i64 2, i64 3, i64 4]
@g.str = internal global [5 x i8] c"hello"
@g = internal global %const_map_int_to_char { i64 5, i64* getelementptr inbounds ([5 x i64], [5 x i64]* @g.keys, i32 0, i32 0), i8* getelementptr inbounds ([5 x i8], [5 x i8]* @g.str, i32 0, i32 0) }
@str = internal global [4 x i8] c"%lu\00"
@str.1 = internal global [2 x i8] c"\0A\00"

declare i32 @printf(i8*, ...)

declare void @memset(i8*, i32, i32)

declare i8* @calloc(i32, i32)

define i64 @main() {
entry:
  %a_1 = alloca i64, align 8
  store i64 1234, i64* %a_1, align 4
  %s_2 = alloca %const_map_int_to_char*, align 8
  store %const_map_int_to_char* @g, %const_map_int_to_char** %s_2, align 8
  %0 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @str, i32 0, i32 0), i64 1234)
  %1 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @str.1, i32 0, i32 0))
  ret i64 0
}
