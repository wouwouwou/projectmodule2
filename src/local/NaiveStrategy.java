package local;

import java.util.*;

import local.Board;

public class NaiveStrategy implements Strategy {

    private String name = "Naive computer -";
    
    @Override
    public String getName() {
	return this.name;
    }

    @Override
    public int determineMove(Board b, Mark m) {
	Set<Integer> emptyFields = new HashSet<Integer>();
	int i = 0;
	while (b.isField(i)) {
	    if (b.isEmptyField(i)) {
		emptyFields.add(i);
	    }
	    i = i + 1;
	}
	int index = (int)Math.round((emptyFields.size() - 1) * Math.random());
	Integer[] array = emptyFields.toArray(new Integer[emptyFields.size()]);
	return array[index];
    }

}
