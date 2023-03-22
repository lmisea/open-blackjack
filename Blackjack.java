public class Blackjack {
    enum Carta {
        TREBOL,
        CORAZON,
        PICA,
        DIAMANTE;
    }        
    static String[] Mazo() {
        int i = 0 ;
        int j = 0 ;
	Carta c1 = Carta.TREBOL;
        Carta c2 = Carta.CORAZON;
        Carta c3 = Carta.DIAMANTE;
        Carta c4 = Carta.PICA;
        String[] id = {"A","2","3","4","5","6","7","8","9","10","J","Q","K", "E"}; 
        String[] Carta = new String[56];
        while (i <= 13) {
            Carta[i] = id[j]+c1;
            j++;
            i++;
        }
        j = 0;
        while (13 < i && i <= 27) {
            Carta[i] = id[j]+c2;
            j++;
            i++;
        }
        j = 0;
        while (27 < i && i <= 41) {
            Carta[i] = id[j]+c3;
            j++;
            i++;
        }
        j = 0;
        while (41 < i && i <= 55) {
            Carta[i] = id[j]+c4;
            j++;
            i++;
        }
        return Carta;
    }
    public static void main(String[] args) {
        int i = 0;
        while (i < 56){        
        	System.out.println(Mazo()[i]);
        	i++;
        }


    }
}
