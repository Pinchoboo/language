fn main(){
	printInt(1234)
	printLn()
	printFloat(5678.9)
	printLn()
	printBool(true)
	printLn()
	printChar('a')
	printLn()
	
	/*
	for loop does not always loop through key value pairs in order, it does for string literals 
	*/
	for _ -> c in "string" {
		printChar(c)
	}
}