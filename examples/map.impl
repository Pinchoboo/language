fn int main(){
	new [int -> int] intmap
	[int -> int] mapref = intmap
	[int -> int] mapref2 = f(intmap)

	printInt(intmap.capacity())
	printLn()
	printInt(mapref.size())
	printLn()
	printInt(mapref2.tombs())
	printLn()

	intmap.insert(1234,5678)

	/* undefined behaviour if the key is not in the map */
	printInt(intmap.get(1234))
	printLn()

	/* use getMaybe when you are not sure whether the key is in the map */ 
	[void -> int] maybevalue = intmap.getMaybe(1234)
	if maybevalue.size() == 1 {
		/* maybevalue has a value */
		int v = maybevalue.get()
	}
	
	if intmap.remove(1234) {
		/* the key 1234 was in the map and now it has been removed */
	}

	intmap.clear()
	/* removed all key value pairs in the map */

	return 0
}

fn [int -> int] f([int -> int] input){
	return input
}