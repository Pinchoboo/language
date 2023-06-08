fn main(){
	printString("Hello World!\n")
}

fn printString(const [int -> char] s) {
	int i = 0
	while i < s.size() {
		printChar(s.get(i))
		i = i + 1
	}
} 