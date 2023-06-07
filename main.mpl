fn int main(){
	new {int -> int} k
	new {{int -> int} -> int} m
	m.getMaybe(k)
	return 0
}