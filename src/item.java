


public class item {

    public static class newitems

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
        //@ requires costofitem<Float.MAX_VALUE;
        //@ ensures costofitem == cost && idofitem == id && itemCount==0;
        //@ ensures costofitem<Float.MAX_VALUE && costofitem>0;
        //@ pure
    public newitems( float costofitem, int idofitem, /*@ non_null @*/ String nameofitem){
        if (nameofitem == null) {
            throw new IllegalArgumentException("Name cannot be null");
        }
        if (costofitem <= 0 || costofitem >= Float.MAX_VALUE) {
            throw new IllegalArgumentException("Invalid cost");
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
    //@ requires item.cost < Float.MAX_VALUE;
    //@ requires 0 <= totalCost - item.cost;
    //@ assigns totalItemCount, totalCost;
    //@ ensures totalItemCount == \old(totalItemCount) - 1;
    //@ ensures \old(totalCost) == totalCost + item.cost;
    public static void removeItemCostToTotalCost(newitems item){
        if(totalCost-item.cost<0||item.cost>=Float.MAX_VALUE||item.cost<=0||totalItemCount<=0){
            return;
        }

        --totalItemCount;
        totalCost-=item.cost;
    }

    //@ requires item != null;
    //@ requires item.cost > 0;
    //@ requires item.cost < Float.MAX_VALUE;
    //@ requires totalCost < Float.MAX_VALUE - item.cost;
    //@ requires totalItemCount <= Integer.MAX_VALUE - 1;
    //@ assigns totalItemCount, totalCost;
    //@ ensures totalItemCount == \old(totalItemCount) + 1;
    //@ ensures totalCost == \old(totalCost) + item.cost;
    //@ ensures item!=null;
    public static void addItem(newitems item) {

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

        totalCost+=item.cost;
        totalItemCount++;

    }

    //@ assignable System.out.outputText, System.out.endsInNewLine;
    public static void printItem(String[] names,newitems[] itemList){
        System.out.println("\nYour Receipt:");
        if(names.length!=itemList.length){
            throw new IllegalStateException("EVIL");
        }
        for(int i=0;i<itemList.length;i++){
            if(i<0){
                throw new IllegalStateException("not valid");
            }
            if(itemList[i]==null){
                throw new IllegalStateException("EVIL");
            }
            if(itemList[i].getItemCount()==0){
                continue;
            }
            System.out.println("\tName: "+names[i]+", Cost: "+itemList[i].cost + ", Quantity: "+ itemList[i].getItemCount());
        }
        System.out.println("\nTotal:\n\tTotal Cost: $"+totalCost+ "\n\tItems In Cart: "+ totalItemCount+"\n");
    }
    //@ requires choice>=0 && choice<itemList.length;
    //@ requires itemList != null;
    //@ ensures itemList[choice] != null;
    //@ ensures itemList[choice].cost > 0;
    //@ ensures itemList[choice].cost < Float.MAX_VALUE;
    //@ ensures itemList[choice].getItemCount() > 0;
    //@ ensures 0 <= totalCost - itemList[choice].cost;
    //@ ensures \result == true;
    //@ assigns \nothing;
    public static boolean removeItemComplete(newitems[] itemList,int choice){
        if(totalItemCount<=0){
            throw new IllegalStateException("Cant Have negative item count");
        }
        if (itemList.length > Integer.MAX_VALUE) {
            throw new IllegalStateException("not valid");
        }

        if (choice >= itemList.length) {
            throw new IllegalStateException("not valid");

        }

        if (choice < 0) {
            throw new IllegalStateException("not valid");
        }
        if(totalCost-itemList[choice].cost<0||itemList[choice].cost>=Float.MAX_VALUE||itemList[choice].cost<=0){
            throw new IllegalStateException("Not Valid Cost.");
        }
        if(itemList[choice].getItemCount()<=0){
            throw new IllegalStateException("Cant have negative count");
        }


        if (itemList[choice] == null) {
            throw new IllegalArgumentException("Item cannot be null.");
        }
        if (itemList[choice].name == null) {
            throw new IllegalArgumentException("Item cannot be null.");
        }
        // @ assume itemList[choice]!= null;
        // @ assume choice< itemList.length;
        // @ assume  itemList[choice].cost>0 && itemList[choice].cost<Float.MAX_VALUE;
        // @ assume choice > -1;
        // @ assume totalCost < Float.MAX_VALUE - itemList[choice].cost;
        // @ assume totalItemCount <= Integer.MAX_VALUE-1;
        return true;
    }

    //@ requires choice>=0 && choice<itemList.length;
    //@ requires itemList != null;
    //@ ensures itemList[choice] != null;
    //@ ensures itemList[choice].cost > 0;
    //@ ensures itemList[choice].cost < Float.MAX_VALUE;
    //@ ensures totalCost < Float.MAX_VALUE - itemList[choice].cost;
    //@ ensures itemList[choice].getItemCount()<=Integer.MAX_VALUE-1;
    //@ ensures totalItemCount <= Integer.MAX_VALUE - 1;
    //@ ensures \result ==true;
    //@ assigns \nothing;
    public static boolean addItemComplete(newitems[] itemList,int choice) {

        if (itemList.length > Integer.MAX_VALUE) {
            throw new IllegalStateException("not valid");
        }

        if (choice >= itemList.length) {
            throw new IllegalStateException("not valid");

        }

        if (choice < 0) {
                throw new IllegalStateException("not valid");
            }

            //@ assume itemList[choice] != null;
            if (itemList[choice].cost <= 0 || itemList[choice].cost >= Float.MAX_VALUE) {
                throw new IllegalStateException("Not Valid Cost.");
            }
            if (totalCost >= Float.MAX_VALUE - itemList[choice].cost) {
                throw new IllegalStateException("Total cost would exceed Float.MAX_VALUE.");
            }
            if (totalItemCount == Integer.MAX_VALUE) {
                throw new IllegalStateException("Too many items.");
            }
            if (itemList[choice] == null) {
                throw new IllegalArgumentException("Item cannot be null.");
            }
            if (itemList[choice].name == null) {
                throw new IllegalArgumentException("Item cannot be null.");
            }
            // @ assume itemList[choice]!= null;
            // @ assume choice< itemList.length;
            // @ assume  itemList[choice].cost>0 && itemList[choice].cost<Float.MAX_VALUE;
            // @ assume choice > -1;
            // @ assume totalCost < Float.MAX_VALUE - itemList[choice].cost;
            // @ assume totalItemCount <= Integer.MAX_VALUE-1;
            if (itemList[choice].getItemCount() == Integer.MAX_VALUE) {
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
        /*@ non_null @*/final newitems apple= new newitems(10,0,name1);
        /*@ non_null @*/final newitems grape= new newitems(90,1,name2);
        /*@ non_null @*/final newitems pear= new newitems(10.50f,2,name3);
        /*@ non_null @*/final newitems mango= new newitems(100,3,name4);
        /*@ non_null @*/final newitems watermelon= new newitems(15,4,name5);
        /*@ non_null @*/final newitems  [] itemList= {apple,grape,pear,mango,watermelon};
        if(addItemComplete(itemList,0)) {
            addItem(itemList[0]);
            itemList[0].addItemCount();
        }
        if(removeItemComplete(itemList,0)){
            removeItemCostToTotalCost(itemList[0]);
            itemList[0].removeItemCount();
        }
        printItem(names,itemList);
      // printItem(names,itemList);

/*
            System.out.println("Welcome to the Shopping Cart Please Select What Action You Would Like To Do:\n \t0: Add Item\n \t1: Remove Item\n \t2: Checkout\n \tElse: Leave" );

            options = scan.nextInt();

            if (options == 0) {
                if(itemList.length!=names.length){
                    throw new IllegalStateException("not valid");
                }
                if(itemList.length>Integer.MAX_VALUE){
                    throw new IllegalStateException("not valid");
                }
                System.out.println("Select Option by ID");
                //@ assume itemList.length==names.length;
                for(int i=0;i<itemList.length;i++){
                    if(i<0){
                        throw new IllegalStateException("not valid");
                    }
                    System.out.println("ID: "+itemList[i].id+ ", Name: "+names[i]+", Cost: "+itemList[i].cost);
                }
                    choice = scan.nextInt();
                    if (choice >=itemList.length) {
                        System.out.println("Not a valid item option");

                    } else {

                        if (choice < 0 || choice > 5) {
                            throw new IllegalStateException("not valid");
                        }

                        //@ assume itemList[choice] != null;
                        if (itemList[choice].cost <= 0 || itemList[choice].cost >= Float.MAX_VALUE) {
                            throw new IllegalStateException("Not Valid Cost.");
                        }
                        if (totalCost >= Float.MAX_VALUE - itemList[choice].cost) {
                            throw new IllegalStateException("Total cost would exceed Float.MAX_VALUE.");
                        }
                        if (totalItemCount == Integer.MAX_VALUE) {
                            throw new IllegalStateException("Too many items.");
                        }
                        if (itemList[choice] == null) {
                            throw new IllegalArgumentException("Item cannot be null.");
                        }
                        if(itemList[choice].name==null){

                        }
                        // @ assume itemList[choice]!= null;
                        // @ assume choice< itemList.length;
                        // @ assume  itemList[choice].cost>0 && itemList[choice].cost<Float.MAX_VALUE;
                        // @ assume choice > -1;
                        // @ assume totalCost < Float.MAX_VALUE - itemList[choice].cost;
                        // @ assume totalItemCount <= Integer.MAX_VALUE-1;
                        if(itemList[choice].getItemCount()==Integer.MAX_VALUE){
                            throw new IllegalStateException("Too many items.");
                        }
                        addItem(itemList[choice]);
                        itemList[choice].addItemCount();
                        System.out.println(names[choice] + " was added successfully!");
                    }

            }
            else if (options==1) {
                System.out.println("Select Option by ID");
                //@ assume itemList.length==names.length;
                for(int i=0;i<itemList.length;i++){
                    if(i<0){
                        throw new IllegalStateException("not valid");
                    }
                    System.out.println("ID: "+itemList[i].id+ ", Name: "+names[i]+", Cost: "+itemList[i].cost);
                }
                choice = scan.nextInt();
                if(choice<0||choice>=itemList.length){
                    throw new IllegalStateException("Not a valid option");
                }
                if(itemList[choice].getItemCount()<=0){
                    throw new IllegalStateException("Cannot remove an item thats not in your cart");
                }
                removeItemCostToTotalCost(itemList[choice]);
                itemList[choice].removeItemCount();
                System.out.println(names[choice] + " was removed successfully!");
            } else if(options==2){
                System.out.println("\nYour Cart:");
                //@ assume itemList.length==names.length;
                for(int i=0;i<itemList.length;i++){
                    if(i<0){
                        throw new IllegalStateException("not valid");
                    }
                    if(itemList[i].getItemCount()<=0){
                        continue;
                    }
                    System.out.println("\tName: "+names[i]+", Cost: "+itemList[i].cost + ", Quantity: "+ itemList[i].getItemCount());
                }
                System.out.println("\nTotal:\n\tTotal Cost: $"+totalCost+ "\n\tItems In Cart: "+ totalItemCount+"\n");

            }
/*
            else if(options==3){
                System.out.println("\nYour Receipt:");
                //@ assume itemList.length==names.length;
                for(int i=0;i<itemList.length;i++){
                    if(i<0){
                        throw new IllegalStateException("not valid");
                    }
                    if(itemList[i].getItemCount()<=0){
                        continue;
                    }
                    System.out.println("\tName: "+names[i]+", Cost: "+itemList[i].cost + ", Quantity: "+ itemList[i].getItemCount());
                }
                System.out.println("\nTotal:\n\tTotal Cost: $"+totalCost+ "\n\tItems In Cart: "+ totalItemCount+"\n");
                break;
            }



        }




*/





    }
}
