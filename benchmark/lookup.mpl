fn int main(){
	int size = 100
	[int->int] m = hashMapFillHalf(size)
	printInt(hashMapLookup(m, size))
	dropHashMap(m)
	return 0
}

fn [int->int] hashMapFillHalf(int size) {
	new [int->int] map
	int idx = 0
	while idx < size {
		map.insert(idx*2, idx)
		idx = idx + 2
	}
	return map
}

fn int hashMapLookup([int->int] map, int size) {
	int idx = 0
	int r = 0
	while idx < size {
		[void -> int] m = map.getMaybe(idx*2)
		if m.size() == 1 {
			r = r + m.get()
		}
		free m
		idx = idx + 1
	}
	return r
}

fn dropHashMap([int->int] map){
	free map
}