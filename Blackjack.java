import java.util.Random;
import java.io.Console;

public class Blackjack {
    enum Carta {
        AT(1),DOST(2),TREST(3),CUATROT(4),CINCOT(5),SEIST(6),SIETET(7),OCHOT(8),NUEVET(9),DIEZT(10),JT(10),QT(10),KT(10),ET(11),
        AC(1),DOSC(2),TRESC(3),CUATROC(4),CINCOC(5),SEISC(6),SIETEC(7),OCHOC(8),NUEVEC(9),DIEZC(10),JC(10),QC(10),KC(10),EC(11),
        AD(1),DOSD(2),TRESD(3),CUATROD(4),CINCOD(5),SEISD(6),SIETED(7),OCHOD(8),NUEVED(9),DIEZD(10),JD(10),QD(10),KD(10),ED(11),
        AP(1),DOSP(2),TRESP(3),CUATROP(4),CINCOP(5),SEISP(6),SIETEP(7),OCHOP(8),NUEVEP(9),DIEZP(10),JP(10),QP(10),KP(10),EP(11);
        
        final int valor;
        Carta (int valor) {
            this.valor = valor;
        }
    }        
    static Carta darCarta(Carta[] a) {
        Random carta = new Random();
        int n = carta.nextInt(56);
        return a[n];
    }
    static int obtenerApuesta(int x) {
        Console con = System.console();
        int apuesta = Integer.parseInt(con.readLine("Para empezar la partida ingresa el monto ha apostar: "));
        while (apuesta > x || apuesta < 10) {
            apuesta = Integer.parseInt(con.readLine("Cantidad erronea, por favor ingrese otro monto: "));
        }
        return apuesta;
    }
    static int valorMano(Carta[] mano, int numCartasMano, int puntosMano) {
        int i = 0;
        while (i < numCartasMano){
            puntosMano = mano[i].valor + puntosMano;
            i++;
        } 
        return puntosMano;
    }

    public static void main(String[] args) {
        Carta mazo[] = Carta.values();
        Carta jugador[] = new Carta[21];
        Carta crupier[] = new Carta[21];
        int credito = 100;

        Console con = System.console();
        String name = con.readLine("Cual es tu nombre ?: ");
        System.out.println("Es un placer tenerte aqui "+name);
        while (credito >= 10){
            int i = 0;
            int j = 2;
            int x = obtenerApuesta(credito);
            while (i < 2) {
                jugador[i] = darCarta(mazo);
                crupier[i] = darCarta(mazo);
                i++;
            }
            int valorJugador = valorMano(jugador, j, 0);
            int valorCrupier = valorMano(crupier, j, 0);   
            System.out.println(valorJugador);
            System.out.println(valorCrupier);

            j = 0;
            while (j < 2) {
                System.out.println(jugador[j]);
                System.out.println(crupier[j]); 
                j++;
    
            }
        }
        System.out.println("El juego se ha terminado");
    }
}
