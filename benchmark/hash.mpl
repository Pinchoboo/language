fn main(){
	
}

fn int fillAndLoop(int size){
	new [int -> void] map
	while map.size() < size{
		map.insert(map.size())
	} 
	for k -> v in map {
		map.remove(k)
	}
	return map.size()
}