[Queue] = [
	HEAD -> [Node]
	TAIL -> [Node]
]

[Node] = [
	NEXT -> [Node]
	VALUE -> int	
]


fn queueInsert([Queue] q, int value) {
	new [Node] nHead
	nHead.insert(VALUE, value)
	[void -> [Node]] maybeOldHead = q.getMaybe(HEAD)
	if maybeOldHead.size() == 1 {
		[Node] oldHead = maybeOldHead.get()
		oldHead.insert(NEXT, nHead)
	}else{
		q.insert(TAIL, nHead)
	}
	q.insert(HEAD, nHead)
}

fn int queueTake([Queue] q) {
	[Node] t = q.get(TAIL)
	int r = t.get(VALUE)
	[void -> [Node]] maybePrev = t.getMaybe(NEXT)
	if maybePrev.size() == 1 {
		[Node] prev = maybePrev.get()
		q.insert(TAIL, prev)
	}else{
		q.remove(TAIL)
	}
	free t
	return r
}

fn bool queueCanTake([Queue] q) {
	[void -> [Node]] m = q.getMaybe(TAIL)
	return m.size() == 1
}