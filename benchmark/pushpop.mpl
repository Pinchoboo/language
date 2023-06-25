fn main(){
	[Vec] v = vecInsertN(11)
	vecTakeN(v, 11)	
}

fn [void -> [Node]] stackInsertN(int s){
	new [void -> [Node]] stack
	int i = 0
	while i < s {
		stackInsert(stack, i)
		i = i + 1
	}
	return stack
}

fn stackTakeN([void -> [Node]] stack, int s){
	int i = 0
	while i < s {
		stackTake(stack)
		i = i + 1
	}
	free stack
}

fn [Queue] queueInsertN(int s){
	new [Queue] q
	int i = 0
	while i < s {
		queueInsert(q, i)
		i = i + 1
	}
	return q
}

fn queueTakeN([Queue] q, int s){
	int i = 0
	while i < s {
		queueTake(q)
		i = i + 1
	}
	free q
}

fn [Vec] vecInsertN(int s){
	new [Vec] v
	new [int->int] d
	v.insert(SIZE, 0)
	v.insert(DATA, d)

	int i = 0
	while i < s {
		vecInsert(v, i)
		i = i + 1
	} 
	return v
}

fn vecTakeN([Vec] v, int s){
	int i = 0
	while i < s {
		vecTake(v)
		i = i + 1
	}
	[int->int] d = v.get(DATA)
	free d
	free v
}


[Node] = [
	NEXT -> [Node]
	VALUE -> int	
]

fn stackInsert([void -> [Node]] head, int value) {
	new [Node] nHead
	nHead.insert(VALUE, value)
	if head.size() == 1 {
		[Node] oldHeadNode = head.get()
		nHead.insert(NEXT, oldHeadNode)
	}
	head.insert(nHead)
}

fn int stackTake([void -> [Node]] head) {
	[Node] oldHeadNode = head.get()
	[void -> [Node]] maybeNHeadNode = oldHeadNode.getMaybe(NEXT)
	if maybeNHeadNode.size() == 1 {
		head.insert(maybeNHeadNode.get())
	}else{
		head.remove()
	}
	int value = oldHeadNode.get(VALUE)
	free oldHeadNode
	free maybeNHeadNode
	return value
}

[Queue] = [
	HEAD -> [Node]
	TAIL -> [Node]
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
	free maybeOldHead
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
	free maybePrev
	free t
	return r
}

[Vec] = [
	SIZE -> int
	DATA -> [int->int]
]

fn vecInsert([Vec] v, int value) {
	[int->int] data = v.get(DATA)
	int idx = v.get(SIZE)
	data.insert(idx,value)
	v.insert(SIZE, idx+1)
}

fn int vecTake([Vec] v) {
	[int->int] data = v.get(DATA)
	int idx = v.get(SIZE) - 1
	v.insert(SIZE, idx)
	int r = data.get(idx)
	data.remove(idx)
	return r
}
