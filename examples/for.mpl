fn main(){
	new [int -> int] map
	map.insert(0,0)
	map.insert(12,34)
	map.insert(56,78)
	for k -> v in map {
		printString("key:")
		printInt(k)
		printString(" maps to value:")
		printInt(v)
		printLn()
	}
}

fn printString(const [int -> char] s) {
	int i = 0
	while i < s.size() {
		printChar(s.get(i))
		i = i + 1
	}
} 