find perfect [float -> int] test = [
	6104.548538707682 -> 0
	2494.622069221747 -> 1
	1790.765590387361 -> 4
	5773.177544944898 -> 9
	3787.061551042865 -> 16
	2569.9022905969036 -> 25
	4155.9633710867265 -> 36
	8204.230117632886 -> 49
	6519.112341600642 -> 64
	8588.633974392671 -> 81
	9449.088871753456 -> 100
	4661.920717251074 -> 121
	7724.920246308186 -> 144
	7742.210845279898 -> 169
	3086.0507251222134 -> 196
	2406.1652360448884 -> 225
]

fn main(){
	float f = 2569.9022905969036
	[void -> int] maybe = test.getMaybe(f)
	if maybe.size() == 1 {
		printInt(maybe.get())
		printLn()
	}
	f = f + 1.0
	maybe = test.getMaybe(f)
	if maybe.size() == 1 {
		printInt(maybe.get())
		printLn()
	}else{
		printString("key: ")
		printFloat(2569.9022905969036 + 1.0)
		printString(" not found, associations are:\n")
		for k -> v in test {
			printFloat(k)
			printString(" -> ")
			printInt(v)
			printLn()
		}
	}
}

fn printString(perfect [int -> char] s) {
	int i = 0
	while i < s.size() {
		printChar(s.get(i))
		i = i + 1
	}
} 