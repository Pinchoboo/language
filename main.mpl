/* {FILOQueue} = {void -> Node} */

{FIFOQueue} = {
	HEAD -> {Node}
	TAIL -> {Node}
}

{Node} = {
	NEXT -> {Node}
	VALUE -> int	
}


fn FIFOinsert({FIFOQueue} q, int value) {
	new {Node} nHead
	nHead.insert(VALUE, value)
	{void -> {Node}} maybeOldHead = q.getMaybe(HEAD)
	if maybeOldHead.size() == 1 {
		{Node} oldHead = maybeOldHead.get()
		oldHead.insert(NEXT, nHead)
	}else{
		q.insert(TAIL, nHead)
	}
	q.insert(HEAD, nHead)
}

fn int FIFOtake({FIFOQueue} q) {
	{Node} t = q.get(TAIL)
	int r = t.get(VALUE)
	{void -> {Node}} maybePrev = t.getMaybe(NEXT)
	if maybePrev.size() == 1 {
		{Node} prev = maybePrev.get()
		q.insert(TAIL, prev)
	}else{
		q.remove(TAIL)
	}
	free t
	return r
}

fn bool FIFOcanTake({FIFOQueue} q) {
	{void -> {Node}} m = q.getMaybe(TAIL)
	return m.size() == 1
}

fn FILOinsert({void -> {Node}} head, int value) {
	new {Node} nHead
	nHead.insert(VALUE, value)
	if head.size() == 1 {
		{Node} oldHeadNode = head.get()
		nHead.insert(NEXT, oldHeadNode)
	}
	head.insert(nHead)
}

fn int FILOtake({void -> {Node}} head) {
	{Node} oldHeadNode = head.get()
	{void -> {Node}} maybeNHeadNode = oldHeadNode.getMaybe(NEXT)
	if maybeNHeadNode.size() == 1 {
		head.insert(maybeNHeadNode.get())
	}else{
		head.remove()
	}
	int value = oldHeadNode.get(VALUE)
	free oldHeadNode
	return value
}

fn bool FILOcanTake({void -> {Node}} head) {
	return head.size() == 1
}

fn int main(){
	new {void -> {Node}} filoQ
	new {FIFOQueue} fifoQ
	int a = 0
	while a < 100 {
		FIFOinsert(fifoQ, a)
		FILOinsert(filoQ, a)
		a = a + 1
	}
	while FIFOcanTake(fifoQ) {
		printInt(FIFOtake(fifoQ))
		printLn()
	}
	while FILOcanTake(filoQ) {
		printInt(FILOtake(filoQ))
		printLn()
	}
	return 0
}