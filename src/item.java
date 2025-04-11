


public class item {

    public static class Items

    {
        public final float cost;
        public final int id;
        //@ non_null
        public final String name;
        //@ spec_public
        private int itemCount;
        // Constructor
        //@ requires costofitem > 0; 
        //@ requires nameofitem!=null;
        //@ requires idofitem>=0 && idofitem<Integer.MAX_VALUE;
        //@ requires costofitem<Float.MAX_VALUE;
        //@ ensures costofitem == cost && idofitem == id && itemCount==0;
        //@ ensures costofitem<Float.MAX_VALUE && costofitem>0;
        //@ ensures id>=0 && id<Integer.MAX_VALUE;
        //@ pure
    public Items(float costofitem, int idofitem, /*@ non_null @*/ String nameofitem){
        if (nameofitem == null) {
            throw new IllegalArgumentException("Name cannot be null");
        }
        if (costofitem <= 0 || costofitem >= Float.MAX_VALUE) {
            throw new IllegalArgumentException("Invalid cost");
        }
        if(idofitem<0||idofitem>=Integer.MAX_VALUE){
            throw new IllegalArgumentException("Invalid ID");
        }
        this.cost = costofitem;
        this.id = idofitem;
        this.name = nameofitem;
        this.itemCount = 0;
    }


        //@ ensures \result == itemCount; // Postcondition: returns the cost
        public /*@ pure @*/ int getItemCount () {
            return itemCount;
        }

        //@ requires itemCount<=Integer.MAX_VALUE-1;
        //@ assigns itemCount;
        //@ ensures itemCount == \old(itemCount)+1;
        public void addItemCount() {

            if (itemCount > Integer.MAX_VALUE - 1) {
                throw new IllegalStateException("Cannot increment itemCount: would cause integer overflow.");
            }


            ++itemCount;
        }

        //@ requires itemCount>0;
        //@ assigns itemCount;
        //@ ensures itemCount == \old(itemCount)-1;
        public void removeItemCount() {
            if (itemCount==0) {
                throw new IllegalStateException("Cannot decriment would lead to underflow");
            }
            --itemCount;
        }
        //@ assigns itemCount;
        //@ ensures itemCount == 0;
        public void resetItemCount() {
            itemCount=0;
        }


        //@ ensures \result == cost; // Postcondition: returns the cost
        public float displayCost () {
        return cost;
    }
        //@ ensures \result.equals(name); // Postcondition: returns the name
        public String displayName () {
        return name;
    }

        //@ ensures \result == id; // Postcondition: returns the id
        public int displayId () {
            return id;
        }
    }

    public static int totalItemCount=0;
    public static float totalCost=0;





    //@ requires item != null;
    //@ requires item.cost > 0;
    //@ requires totalItemCount > 0;
    //@ requires item.getItemCount()>0;
    //@ requires item.cost < Float.MAX_VALUE;
    //@ requires 0 <= totalCost - item.cost;
    //@ assigns totalItemCount, totalCost,item.itemCount;
    //@ ensures totalItemCount == \old(totalItemCount) - 1;
    //@ ensures item.itemCount==\old(item.itemCount)-1;
    //@ ensures \old(totalCost) == totalCost + item.cost;
    public static void removeItemCostToTotalCost(Items item){
        if(totalCost-item.cost<0||item.cost>=Float.MAX_VALUE||item.cost<=0||totalItemCount<=0){
            throw new IllegalStateException("bad invocation");
        }
        if(item.getItemCount()<=0){
            throw new IllegalStateException("Cant have negative count");
        }
        item.removeItemCount();
        --totalItemCount;
        totalCost-=item.cost;
    }

    //@ requires item != null;
    //@ requires item.cost > 0;
    //@ requires item.itemCount<Integer.MAX_VALUE;
    //@ requires item.cost < Float.MAX_VALUE;
    //@ requires totalCost < Float.MAX_VALUE - item.cost;
    //@ requires totalItemCount <= Integer.MAX_VALUE - 1;
    //@ assigns totalItemCount, totalCost,item.itemCount;
    //@ ensures totalItemCount == \old(totalItemCount) + 1;
    //@ ensures totalCost == \old(totalCost) + item.cost;
    //@ ensures item.itemCount== \old(item.itemCount)+1;
    //@ ensures item!=null;
    public static void addItem(Items item) {

        if (item == null) {
            throw new IllegalArgumentException("Item cannot be null.");
        }
        if (item.cost <= 0 || item.cost >= Float.MAX_VALUE) {
            throw new IllegalStateException("Not Valid Cost.");
        }
        if (totalCost >= Float.MAX_VALUE - item.cost) {
            throw new IllegalStateException("Total cost would exceed Float.MAX_VALUE.");
        }
        if (totalItemCount == Integer.MAX_VALUE) {
            throw new IllegalStateException("Too many items.");
        }
        if(item.getItemCount()==Integer.MAX_VALUE){
            throw new IllegalStateException("Overflow");
        }
        item.addItemCount();
        totalCost+=item.cost;
        totalItemCount++;

    }

    //@ assignable System.out.outputText, System.out.endsInNewLine;
    public static void printItem(String[] names, Items[] ShoppingCart){
        System.out.println("\nYour Receipt:");
        if(names.length!=ShoppingCart.length){
            throw new IllegalStateException("EVIL");
        }
        for(int i=0;i<ShoppingCart.length;i++){
            if(i<0){
                throw new IllegalStateException("not valid");
            }
            if(ShoppingCart[i]==null){
                throw new IllegalStateException("EVIL");
            }
            if(ShoppingCart[i].getItemCount()==0){
                continue;
            }
            System.out.println("\tName: "+names[i]+", Cost: "+ShoppingCart[i].cost + ", Quantity: "+ ShoppingCart[i].getItemCount());
        }
        System.out.println("\nTotal:\n\tTotal Cost: $"+totalCost+ "\n\tItems In Cart: "+ totalItemCount+"\n");
    }
    //@ requires choice>=0 && choice<ShoppingCart.length;
    //@ requires ShoppingCart != null;
    //@ ensures ShoppingCart[choice] != null;
    //@ ensures ShoppingCart[choice].cost > 0;
    //@ ensures ShoppingCart[choice].cost < Float.MAX_VALUE;
    //@ ensures ShoppingCart[choice].getItemCount() > 0;
    //@ ensures 0 <= totalCost - ShoppingCart[choice].cost;
    //@ ensures \result == true;
    //@ assigns \nothing;
    public static boolean removeItemComplete(Items[] ShoppingCart, int choice){
        if(totalItemCount<=0){
            throw new IllegalStateException("Cant Have negative item count");
        }
        if (ShoppingCart.length > Integer.MAX_VALUE) {
            throw new IllegalStateException("not valid");
        }

        if (choice >= ShoppingCart.length) {
            throw new IllegalStateException("not valid");

        }

        if (choice < 0) {
            throw new IllegalStateException("not valid");
        }
        if(totalCost-ShoppingCart[choice].cost<0||ShoppingCart[choice].cost>=Float.MAX_VALUE||ShoppingCart[choice].cost<=0){
            throw new IllegalStateException("Not Valid Cost.");
        }
        if(ShoppingCart[choice].getItemCount()<=0){
            throw new IllegalStateException("Cant have negative count");
        }


        if (ShoppingCart[choice] == null) {
            throw new IllegalArgumentException("Item cannot be null.");
        }
        if (ShoppingCart[choice].name == null) {
            throw new IllegalArgumentException("Item cannot be null.");
        }
        // @ assume ShoppingCart[choice]!= null;
        // @ assume choice< ShoppingCart.length;
        // @ assume  ShoppingCart[choice].cost>0 && ShoppingCart[choice].cost<Float.MAX_VALUE;
        // @ assume choice > -1;
        // @ assume totalCost < Float.MAX_VALUE - ShoppingCart[choice].cost;
        // @ assume totalItemCount <= Integer.MAX_VALUE-1;
        return true;
    }

    //@ requires choice>=0 && choice<ShoppingCart.length;
    //@ requires ShoppingCart != null;
    //@ ensures ShoppingCart[choice] != null;
    //@ ensures ShoppingCart[choice].cost > 0;
    //@ ensures ShoppingCart[choice].cost < Float.MAX_VALUE;
    //@ ensures totalCost < Float.MAX_VALUE - ShoppingCart[choice].cost;
    //@ ensures ShoppingCart[choice].getItemCount()<=Integer.MAX_VALUE-1;
    //@ ensures totalItemCount <= Integer.MAX_VALUE - 1;
    //@ ensures \result ==true;
    //@ assigns \nothing;
    public static boolean addItemComplete(Items[] ShoppingCart, int choice) {

        if (ShoppingCart.length > Integer.MAX_VALUE) {
            throw new IllegalStateException("not valid");
        }

        if (choice >= ShoppingCart.length) {
            throw new IllegalStateException("not valid");

        }

        if (choice < 0) {
                throw new IllegalStateException("not valid");
            }

            //@ assume ShoppingCart[choice] != null;
            if (ShoppingCart[choice].cost <= 0 || ShoppingCart[choice].cost >= Float.MAX_VALUE) {
                throw new IllegalStateException("Not Valid Cost.");
            }
            if (totalCost >= Float.MAX_VALUE - ShoppingCart[choice].cost) {
                throw new IllegalStateException("Total cost would exceed Float.MAX_VALUE.");
            }
            if (totalItemCount == Integer.MAX_VALUE) {
                throw new IllegalStateException("Too many items.");
            }
            if (ShoppingCart[choice] == null) {
                throw new IllegalArgumentException("Item cannot be null.");
            }
            if (ShoppingCart[choice].name == null) {
                throw new IllegalArgumentException("Item cannot be null.");
            }
            // @ assume ShoppingCart[choice]!= null;
            // @ assume choice< ShoppingCart.length;
            // @ assume  ShoppingCart[choice].cost>0 && ShoppingCart[choice].cost<Float.MAX_VALUE;
            // @ assume choice > -1;
            // @ assume totalCost < Float.MAX_VALUE - ShoppingCart[choice].cost;
            // @ assume totalItemCount <= Integer.MAX_VALUE-1;
            if (ShoppingCart[choice].getItemCount() == Integer.MAX_VALUE) {
                throw new IllegalStateException("Too many items.");
            }
            return true;


    }


    public static void main(String args[]){

        int choice=0;
        int options=0;
        /*@ non_null @*/ String name1="Apple";
        /*@ non_null @*/String name2="Grape";
        /*@ non_null @*/String name3="Pear";
        /*@ non_null @*/String name4="Mango";
        /*@ non_null @*/String name5="Watermelon";
        /*@ non_null @*/ final String[] names= {name1,name2,name3,name4,name5};
        /*@ non_null @*/final Items apple= new Items(10,0,name1);
        /*@ non_null @*/final Items grape= new Items(90,1,name2);
        /*@ non_null @*/final Items pear= new Items(10.50f,2,name3);
        /*@ non_null @*/final Items mango= new Items(100,3,name4);
        /*@ non_null @*/final Items watermelon= new Items(15,4,name5);
        /*@ non_null @*/final Items[] ShoppingCart= {apple,grape,pear,mango,watermelon};
        if(addItemComplete(ShoppingCart,0)) {
            addItem(ShoppingCart[0]);
        }

        if(removeItemComplete(ShoppingCart,0)){
            removeItemCostToTotalCost(ShoppingCart[0]);
        }
        if(removeItemComplete(ShoppingCart,0)){
            removeItemCostToTotalCost(ShoppingCart[0]);
        }
        printItem(names,ShoppingCart);
      // printItem(names,ShoppingCart);

/*
            System.out.println("Welcome to the Shopping Cart Please Select What Action You Would Like To Do:\n \t0: Add Item\n \t1: Remove Item\n \t2: Checkout\n \tElse: Leave" );

            options = scan.nextInt();

            if (options == 0) {
                if(ShoppingCart.length!=names.length){
                    throw new IllegalStateException("not valid");
                }
                if(ShoppingCart.length>Integer.MAX_VALUE){
                    throw new IllegalStateException("not valid");
                }
                System.out.println("Select Option by ID");
                //@ assume ShoppingCart.length==names.length;
                for(int i=0;i<ShoppingCart.length;i++){
                    if(i<0){
                        throw new IllegalStateException("not valid");
                    }
                    System.out.println("ID: "+ShoppingCart[i].id+ ", Name: "+names[i]+", Cost: "+ShoppingCart[i].cost);
                }
                    choice = scan.nextInt();
                    if (choice >=ShoppingCart.length) {
                        System.out.println("Not a valid item option");

                    } else {

                        if (choice < 0 || choice > 5) {
                            throw new IllegalStateException("not valid");
                        }

                        //@ assume ShoppingCart[choice] != null;
                        if (ShoppingCart[choice].cost <= 0 || ShoppingCart[choice].cost >= Float.MAX_VALUE) {
                            throw new IllegalStateException("Not Valid Cost.");
                        }
                        if (totalCost >= Float.MAX_VALUE - ShoppingCart[choice].cost) {
                            throw new IllegalStateException("Total cost would exceed Float.MAX_VALUE.");
                        }
                        if (totalItemCount == Integer.MAX_VALUE) {
                            throw new IllegalStateException("Too many items.");
                        }
                        if (ShoppingCart[choice] == null) {
                            throw new IllegalArgumentException("Item cannot be null.");
                        }
                        if(ShoppingCart[choice].name==null){

                        }
                        // @ assume ShoppingCart[choice]!= null;
                        // @ assume choice< ShoppingCart.length;
                        // @ assume  ShoppingCart[choice].cost>0 && ShoppingCart[choice].cost<Float.MAX_VALUE;
                        // @ assume choice > -1;
                        // @ assume totalCost < Float.MAX_VALUE - ShoppingCart[choice].cost;
                        // @ assume totalItemCount <= Integer.MAX_VALUE-1;
                        if(ShoppingCart[choice].getItemCount()==Integer.MAX_VALUE){
                            throw new IllegalStateException("Too many items.");
                        }
                        addItem(ShoppingCart[choice]);
                        ShoppingCart[choice].addItemCount();
                        System.out.println(names[choice] + " was added successfully!");
                    }

            }
            else if (options==1) {
                System.out.println("Select Option by ID");
                //@ assume ShoppingCart.length==names.length;
                for(int i=0;i<ShoppingCart.length;i++){
                    if(i<0){
                        throw new IllegalStateException("not valid");
                    }
                    System.out.println("ID: "+ShoppingCart[i].id+ ", Name: "+names[i]+", Cost: "+ShoppingCart[i].cost);
                }
                choice = scan.nextInt();
                if(choice<0||choice>=ShoppingCart.length){
                    throw new IllegalStateException("Not a valid option");
                }
                if(ShoppingCart[choice].getItemCount()<=0){
                    throw new IllegalStateException("Cannot remove an item thats not in your cart");
                }
                removeItemCostToTotalCost(ShoppingCart[choice]);
                ShoppingCart[choice].removeItemCount();
                System.out.println(names[choice] + " was removed successfully!");
            } else if(options==2){
                System.out.println("\nYour Cart:");
                //@ assume ShoppingCart.length==names.length;
                for(int i=0;i<ShoppingCart.length;i++){
                    if(i<0){
                        throw new IllegalStateException("not valid");
                    }
                    if(ShoppingCart[i].getItemCount()<=0){
                        continue;
                    }
                    System.out.println("\tName: "+names[i]+", Cost: "+ShoppingCart[i].cost + ", Quantity: "+ ShoppingCart[i].getItemCount());
                }
                System.out.println("\nTotal:\n\tTotal Cost: $"+totalCost+ "\n\tItems In Cart: "+ totalItemCount+"\n");

            }
/*
            else if(options==3){
                System.out.println("\nYour Receipt:");
                //@ assume ShoppingCart.length==names.length;
                for(int i=0;i<ShoppingCart.length;i++){
                    if(i<0){
                        throw new IllegalStateException("not valid");
                    }
                    if(ShoppingCart[i].getItemCount()<=0){
                        continue;
                    }
                    System.out.println("\tName: "+names[i]+", Cost: "+ShoppingCart[i].cost + ", Quantity: "+ ShoppingCart[i].getItemCount());
                }
                System.out.println("\nTotal:\n\tTotal Cost: $"+totalCost+ "\n\tItems In Cart: "+ totalItemCount+"\n");
                break;
            }



        }




*/





    }
}
