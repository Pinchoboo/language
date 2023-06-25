/* main function is the entry point to the program*/
fn int main(){
	/* basic variable types */
	int i = 1 + 1
	bool b = true
	char c = 'c'
	float f = 1234.5436

	/* reasignment */
	i = i * i

	/* if, if else, else blocks */
	if i > 3 {

	}else if b {

	}else{

	}

	/*while loop */
	while i < 10 {
		i = i + 1
	}

	/* print functions */
	
	printInt(i)
	printLn()
	printFloat(f)
	printLn()
	printBool(b)
	printLn()
	printChar(c)
	printLn()
	
	/* allocate a new map from ints to ints */
	new [int -> int] intmap
	
	/* this map refers to the same heap allocated map */
	[int -> int] mapref = intmap

	/* get the capacity of the map */
	printInt(intmap.capacity())
	printLn()
	/* get the number of keay value pairs of the map */
	printInt(mapref.size())
	printLn()
	/* get the number of tombs in the map */
	printInt(intmap.tombs())
	printLn()

	/* insert key 1234 and value 5678 */
	intmap.insert(1234,5678)

	/* get the value associated with the key 1234, undefined behaviour if the key is not in the map */
	printInt(intmap.get(1234))
	printLn()

	/* 
		use getMaybe when you are not sure whether the key is in the map
		it creates a new map that is filled with the value associated with key 1234 if it exists
	*/ 
	[void -> int] maybevalue = intmap.getMaybe(1234)
	
	if maybevalue.size() == 1 {
		/* maybevalue has a value */
		int v = maybevalue.get()
	}
	
	if intmap.remove(1234) {
		/* the key 1234 was in the map and now it has been removed */
	}
	
	/* clears all key value pairs and resizes to minimum size */ 
	intmap.clear()

	/* need to manually free maps when you dont use them anymore */
	free intmap
	free maybevalue

	/* perfect hashmaps have no collisions but can not be resized */
	perfect [int -> char] s = "string literals are of type perfect[int to char]"

	/* or loop does not always loop through key value pairs in order, it does for string literals */
	for indexKey -> associatedCharacte in "hello\n" {
		printChar(associatedCharacte)
	}
	
	/* function calls*/
	int fibresult = fib(10)
	
	/* zero exit code*/
	return 0
}

/* function definition */
fn int fib(int x) {
	if x < 2 {
		return 1
	}
	return fib(x-1) + fib(x-2)
}

/* last type of map */

[LinkedListNode] = [
	NEXT -> [LinkedListNode]
	VALUE -> int
]

fn linkedListfn(){
	/* allocate new map */
	new [LinkedListNode] ll

	/*same functions as the other maps */
	ll.insert(VALUE, 1234)
	[void -> [LinkedListNode]] maybeNextNode = ll.getMaybe(NEXT)
	free ll
	free maybeNextNode
}