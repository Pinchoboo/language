[BTree] = [
	VALUE -> int
	LEFT -> [BTree]
	RIGHT -> [BTree]
]

fn main(){
	printInt(heapSize())
	printLn()
	new [BTree] tree
	printInt(heapSize())
	printLn()
	
	printString("Hello World!\n")
}

fn printString(perfect [int -> char] s) {
	int i = 0
	while i < s.size() {
		printChar(s.get(i))
		i = i + 1
	}
} 