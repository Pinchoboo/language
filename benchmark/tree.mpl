fn main(){
	[void->[BTree]] t = BTreeFill(220)
	BTreeEmpty(t, 220)
	BTreeFree(t)
}

fn [void->[BTree]] BTreeFill(int s){
	new [void->[BTree]] tree 
	int idx = 0 
	int val = s/2
	while idx < s {
		BTreeInsert(tree, val%s)
		idx = idx + 1
		val = val * 3 + idx
	}
	return tree
}

fn  BTreeEmpty([void->[BTree]] tree, int s){
	int idx = 0 
	int val = s
	while idx < s {
		BTreeRemove(tree, idx)
		idx = idx + 1
	}
	
}

[BTree] = [
	VALUE -> int
	LEFT -> [BTree]
	RIGHT -> [BTree]
]

fn BTreeInsert([void -> [BTree]] bt, int val) {
	new [BTree] leaf
	leaf.insert(VALUE, val)
	if bt.size() == 0 {
		bt.insert(leaf)
		return
	}
	[BTree] current = bt.get()
	while true {
		if current.get(VALUE) > val {
			[void->[BTree]] next = current.getMaybe(LEFT)
			if next.size() == 0 {
				current.insert(LEFT,leaf)
				return
			}
			current = next.get()
			free next
		} else {
			[void->[BTree]] next = current.getMaybe(RIGHT)
			if next.size() == 0 {
				current.insert(RIGHT,leaf)
				return
			}
			current = next.get()
			free next
		}
	}
}

fn bool BTreeContains([void -> [BTree]] bt, int val) {
	if bt.size() == 0 {
		return false
	}
	[BTree] current = bt.get()
	int cv = current.get(VALUE)
	new [void->[BTree]] child
	while cv != val {
		if val < cv {
			free child
			child = current.getMaybe(LEFT)
		}else{
			free child
			child = current.getMaybe(RIGHT)
		}
		if child.size() == 0 {
			return false
		}
		current = child.get()
		cv = current.get(VALUE)
	}
	free child
	return true
}

fn [void -> [BTree]] BTreeRemove([void -> [BTree]] mbt, int val) {
	if mbt.size() == 0 {
		return mbt
	}
	
	[BTree] bt = mbt.get()
	int btval = bt.get(VALUE)
	if btval > val {
		[void -> [BTree]] ptr = bt.getMaybe(LEFT) 
		if ptr.size() == 1 {
			BTreeRemove(ptr, val)
			if ptr.size() == 1 {
				bt.insert(LEFT, ptr.get())
			}else{
				bt.remove(LEFT)
			}
		}
		free ptr
	} else if btval < val {
		[void -> [BTree]] ptr = bt.getMaybe(RIGHT) 
		if ptr.size() == 1 {
			BTreeRemove(ptr, val)
			if ptr.size() == 1 {
				bt.insert(RIGHT, ptr.get())
			}else{
				bt.remove(RIGHT)
			}
		}
		free ptr
	}else{
		[void -> [BTree]] ptrl = bt.getMaybe(LEFT)
		[void -> [BTree]] ptrr = bt.getMaybe(RIGHT)
		int numchild = ptrl.size() + ptrr.size()
		
		if numchild == 0 {
			mbt.remove()
			free bt
		}else if numchild == 1 {
			if ptrl.size() == 1 {
				mbt.insert(ptrl.get())
			}else{
				mbt.insert(ptrr.get())
			}
			free bt
		}else{
			[BTree] succParent = bt /* 4 */
			[BTree] succ = ptrr.get() /* 6 */
			free ptrl
			ptrl = succ.getMaybe(LEFT) /* 6L */
			bool isroot = true
			while ptrl.size() == 1 {
				isroot = false
				succParent = succ 
				succ = ptrl.get() 
				free ptrl
				ptrl = succ.getMaybe(LEFT) 
			}
			free ptrr 
			ptrr = succ.getMaybe(RIGHT) /* 6R */
			if ptrr.size() == 1 {
				if isroot {
					succParent.insert(RIGHT,ptrr.get())
				}else{
					succParent.insert(LEFT,ptrr.get())
				}
			}else{
				bt.insert(VALUE, succ.get(VALUE))
				if isroot {
					succParent.remove(RIGHT)
				} else {
					succParent.remove(LEFT)
				}
				free succ
			}
		}
		free ptrl
		free ptrr
	}
	return mbt
}

fn BTreePrintInOrder([void -> [BTree]] mbt) {
	_BTreePrintInOrder(mbt, 0)
}

fn _BTreePrintInOrder([void -> [BTree]] mbt, int indent) {
	if mbt.size() == 0 {
		return
	}
	[BTree] bt = mbt.get()
	[void -> [BTree]] ptr = bt.getMaybe(RIGHT)
	_BTreePrintInOrder(ptr, indent + 1)
	free ptr
	int idx = 0
	while idx < indent {
		printChar('	')
		idx = idx + 1
	}
	printInt(bt.get(VALUE))
	printLn()
	ptr = bt.getMaybe(LEFT)
	_BTreePrintInOrder(ptr, indent + 1)
	free ptr
}

fn BTreeFree([void -> [BTree]] mbt) {
	if mbt.size() == 0 {
		free mbt
		return
	}
	[BTree] bt = mbt.get()
	BTreeFree(bt.getMaybe(RIGHT))
	BTreeFree(bt.getMaybe(LEFT))
	free bt
	free mbt
}