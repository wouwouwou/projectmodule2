package local;

import local.Board;

public interface Strategy {
    
    public String getName();
    
    public int determineMove(Board b, Mark m);

}
