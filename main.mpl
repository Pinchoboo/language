fn main(){
	dropHashSet(hashSetFill(100))
}

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