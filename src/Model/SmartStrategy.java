package Model;

import java.util.HashSet;
import java.util.Set;

public class SmartStrategy implements Strategy {
    
    private String name = "Smart computer -";

    @Override
    public String getName() {
	return this.name;
    }

    @Override
    public int determineMove(Board b, Mark m) {
	if (b.isEmptyField(4)) {
	    return 4;
	}
	
	Board copy = b.deepCopy();
	int i = 0;
	while (b.isField(i)) {
	    if (b.isEmptyField(i)) {
		copy.setField(i, m);
		if (copy.isWinner(m)) {
		    return i;
		}
		copy = b.deepCopy();
	    }
	    i++;
	}
	
	i = 0;
	while (b.isField(i)) {
	    if (b.isEmptyField(i)) {
		copy.setField(i, m.other());
		if (copy.isWinner(m.other())) {
		    return i;
		}
		copy = b.deepCopy();
	    }
	    i++;
	}
	
	Set<Integer> emptyFields = new HashSet<Integer>();
	i = 0;
	while (b.isField(i)) {
	    if (b.isEmptyField(i)) {
		emptyFields.add(i);
	    }
	    i++;
	}
	int index = (int)Math.round((emptyFields.size() - 1) * Math.random());
	Integer[] array = emptyFields.toArray(new Integer[emptyFields.size()]);
	return array[index];
    }

}
