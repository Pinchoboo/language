fn main(){}

fn [int->int] hashMapFillHalf(int size) {
	new [int->int] map
	int idx = 0
	while idx < size {
		map.insert(idx, 0)
		idx = idx + 2
	}
	return map
}

fn int hashMapLookup([int->int] map, int size) {
	int idx = 0
	int r = 0
	while idx < size {
		[void -> int] m = map.getMaybe(idx)
		if m.size() == 1 {
			r = r + 1
		}
		idx = idx + 1
	}
	return r
}

fn dropHashMap([int->int] map){
	free map
}