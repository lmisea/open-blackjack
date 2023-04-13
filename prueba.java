public class prueba {
    static int myMethod(int x, int y) {
        while (x < y){
            if (x == 7)
                return x;
            x++;
        }
        return x;
    }
    public static void main(String[] args) {
        System.out.println(myMethod(3, 8));
      }
}
