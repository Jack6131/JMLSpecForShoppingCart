import java.util.HashMap;
import java.util.Map;

public class BasicHashMapExample {

    //@ public static model Map<Integer, String> map;
    //@ public static invariant map != null;  // The map should not be null

    public static void main(String[] args) {
        // Initialize the map as a new HashMap
        Map<Integer, String> map = new HashMap<>();

        // Add some key-value pairs to the map
        //@ ensures map.containsKey(1) && map.get(1).equals("Apple");
        //@ ensures map.containsKey(2) && map.get(2).equals("Banana");
        //@ ensures map.containsKey(3) && map.get(3).equals("Cherry");
        map.put(1, "Apple");
        map.put(2, "Banana");
        map.put(3, "Cherry");

        // Retrieve a value using its key
        //@ assert map.get(1).equals("Apple");
        System.out.println("Key 1: " + map.get(1));  // Output: Apple

        //@ assert map.get(2).equals("Banana");
        System.out.println("Key 2: " + map.get(2));  // Output: Banana

        // Check if a key exists in the map
        //@ assert map.containsKey(3);
        if (map.containsKey(3)) {
            System.out.println("Key 3 exists: " + map.get(3));  // Output: Cherry
        }

        // Remove a key-value pair
        //@ ensures !map.containsKey(2);
        map.remove(2);

        // Check if key 2 exists after removal
        //@ assert !map.containsKey(2);
        System.out.println("Contains key 2: " + map.containsKey(2));  // Output: false

        // Print all key-value pairs in the map
        System.out.println("\nAll items in the map:");
        //@ foreach Map.Entry<Integer, String> entry in map.entrySet();
        //@ ensures map.containsKey(entry.getKey()) && map.get(entry.getKey()).equals(entry.getValue());
        for (Map.Entry<Integer, String> entry : map.entrySet()) {
            System.out.println(entry.getKey() + " -> " + entry.getValue());
        }
    }
}
