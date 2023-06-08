[RecursiveMap] = [
	NEXT => [RecursiveMap]
	VALUE = int
]

fn main(){
	new [RecursiveMap] rm
	rm.insert(VALUE, 1234)
	new [RecursiveMap] previous
	previous.insert(NEXT, rm)
}