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
	return value
}

fn bool stackCanTake([void -> [Node]] head) {
	return head.size() == 1
}
