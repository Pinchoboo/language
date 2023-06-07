fn int main(){
	new {void -> void} E
	new {void -> void} F
	F.insert()
	new {{void -> void} -> {void -> void}} M
	M.insert(F,E)
	{void -> {void -> void}} R = M.getMaybe(F)
	printInt(R.size())
	printLn()
	return 0
}