fn int main(){
	printString(
"
Hello World!
"
	)
	return 0
}

fn printString(const {int -> char} s) {
	int i = 0
	while i < s.size() {
		printChar(s.get(i))
		i = i + 1
	}
} 