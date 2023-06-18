fn main(){}

fn [int->void] hashSetFill(int size) {
	new [int->void] set
	while set.size() < size {
		set.insert(set.size())
	}
	return set
}

fn dropHashSet([int->void] set){
	free set
}

fn [int->int] hashMapFill(int size) {
	new [int->int] map
	while map.size() < size {
		map.insert(map.size(),map.size())
	}
	return map
}

fn dropHashMap([int->int] map){
	free map
}