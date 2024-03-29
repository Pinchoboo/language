fn int main(){
	printInt(heapSize())
	printLn()
	[int->void] m = hashSetFill(100000000)
	printInt(heapSize())
	printLn()
	free m
	printInt(heapSize())
	printLn()
	return 0
}

fn [int->void] hashSetFill(int size) {
	new [int->void] set
	while set.size() < size {
		set.insert(set.size()*7)
	}
	return set
}

fn dropHashSet([int->void] set){
	free set
}

fn [float->void] hashSetFloatFill(int size) {
	new [float->void] set
	float f = 0.0
	while set.size() < size {
		set.insert(f*1.1)
		f = f + 1.0
	}
	return set
}

fn dropHashSetFloat([float->void] set){
	free set
}

fn [int->int] hashMapFill(int size) {
	new [int->int] map
	while map.size() < size {
		map.insert(map.size()*7,map.size())
	}
	return map
}

fn dropHashMap([int->int] map){
	free map
}

fn printString(perfect [int -> char] s) {
	int i = 0
	while i < s.size() {
		printChar(s.get(i))
		i = i + 1
	}
} 