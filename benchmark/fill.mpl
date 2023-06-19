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

fn [float->void] hashSetFloatFill(int size) {
	new [float->void] set
	float f = 0.0
	while set.size() < size {
		set.insert(f)
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
		map.insert(map.size(),map.size())
	}
	return map
}

fn dropHashMap([int->int] map){
	free map
}