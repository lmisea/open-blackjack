import java.io.Console;
import java.util.Random;

public class Blackjack {
    // Creacion de todas las posibles cartas

    enum Carta {
        AS_PICAS, DOS_PICAS, TRES_PICAS, CUATRO_PICAS,
        CINCO_PICAS, SEIS_PICAS, SIETE_PICAS, OCHO_PICAS,
        NUEVE_PICAS, DIEZ_PICAS, J_PICAS, Q_PICAS,
        K_PICAS, COMODÍN_PICAS, AS_DIAMANTE, DOS_DIAMANTE,
        TRES_DIAMANTE, CUATRO_DIAMANTE, CINCO_DIAMANTE, SEIS_DIAMANTE,
        SIETE_DIAMANTE, OCHO_DIAMANTE, NUEVE_DIAMANTE, DIEZ_DIAMANTE,
        J_DIAMANTE, Q_DIAMANTE, K_DIAMANTE, COMODÍN_DIAMANTE,
        AS_TREBOL, DOS_TREBOL, TRES_TREBOL, CUATRO_TREBOL,
        CINCO_TREBOL, SEIS_TREBOL, SIETE_TREBOL, OCHO_TREBOL,
        NUEVE_TREBOL, DIEZ_TREBOL, J_TREBOL, Q_TREBOL,
        K_TREBOL, COMODÍN_TREBOL, AS_CORAZON, DOS_CORAZON,
        TRES_CORAZON, CUATRO_CORAZON, CINCO_CORAZON, SEIS_CORAZON,
        SIETE_CORAZON, OCHO_CORAZON, NUEVE_CORAZON, DIEZ_CORAZON,
        J_CORAZON, Q_CORAZON, K_CORAZON, COMODÍN_CORAZON;

        private Carta() {
        }
    }

    // Metodos para obtener informacion de las cartas que se repartan aleatoriamente

    //@ requires carta != null;
    //@ ensures \result == "Picas" || \result == "Diamantes" || \result == "Treboles" || \result == "Corazones";
    public static /*@ pure @*/ String obtenerPaloCarta(Carta carta) {
        if (carta.ordinal() <= 13)
            return "Picas";
        else if (carta.ordinal() <= 27)
            return "Diamantes";
        else if (carta.ordinal() <= 41)
            return "Treboles";
        else
            return "Corazones";
    }

    //@ requires carta != null;
    //@ ensures 0 < \result <= 11;
    public static /*@ pure @*/ int obtenerValorCarta(Carta carta) {
        if (carta.ordinal() % 14 <= 9)
            return (carta.ordinal() % 14) + 1;
        else if (carta.ordinal() % 14 <= 12)
            return 10;
        else
            return 11;
    }

    //@ requires carta != null;
    //@ ensures \result.equals("A") || \result.equals("J") || \result.equals("Q") || \result.equals("K") || \result.equals("Joker") || 2 <= Integer.parseInt(\result) <= 10;
    public static /*@ pure @*/ String obtenerNombreCarta(Carta carta) {
        if (carta.ordinal() % 14 == 0)
            return "A";
        else if (carta.ordinal() % 14 <= 9)
            return Integer.toString((carta.ordinal() % 14) + 1);
        else if (carta.ordinal() % 14 == 10)
            return "J";
        else if (carta.ordinal() % 14 == 11)
            return "Q";
        else if (carta.ordinal() % 14 == 12)
            return "K";
        else
            return "Joker";
    }

    // Función Repartir una Carta

    //@ requires baraja.length == 56;
    //@ ensures (\exists int i; 0 <= i && i < baraja.length; \result == baraja[i]);
    public static /*@ pure @*/ Carta darCarta(Carta[] baraja) {
        Random carta = new Random();
        int aleatorio = carta.nextInt(56);
        //@ assert aleatorio >= 0 && aleatorio < 56 ;
        return baraja[aleatorio];
    }

    // Función Obtener monto de la apuesta

    //@ requires credito >= 10 && credito < Integer.MAX_VALUE / 2;
    //@ ensures \result >= 10 && \result <= credito;
    public static int obtenerApuesta(int credito, Console con) {
        int i = 0;
        int apuesta = Integer.parseInt(con.readLine("Para empezar la partida ingresa el monto ha apostar: "));
        //@ assert String.valueOf(apuesta) != null;

        //@ maintaining 0 <= i <= 5;
        //@ maintaining (\forall int k; 0 <= k && k < i; apuesta > credito || apuesta < 10 || apuesta <= credito || apuesta >= 10 );
        //@ decreases 5 - i;
        while (i < 5) {
            if (i == 4) {
                System.out.println("Se le ha establecido la apuesta minima");
                apuesta = 10;
                break;
            } else if (apuesta > credito || apuesta < 10) {
                apuesta = Integer.parseInt(con.readLine("Cantidad erronea, por favor ingrese otro monto: "));
                i++;
            } else if (apuesta <= credito && apuesta >= 10) {
                break;
            }
        }
        return apuesta;
    }

    // Función Determinar el valor de una mano

    //@ requires 0 < manoJugador.length <= 21;
    //@ requires 2 <= numCartasMano <= 21;
    //@ ensures 2 <= \result <= 31;
    public static /*@ pure @*/ int valorMano(Carta[] manoJugador, int numCartasMano) {
        int i = 0;
        int puntosMano = 0;

        //@ maintaining 0 <= i <= numCartasMano;
        //@ maintaining 2 <= numCartasMano <= 21;
        //@ maintaining (\forall int k; 0 <= k && k < i; 2 <= puntosMano <= 31);
        //@ decreases numCartasMano - i;
        while (i < numCartasMano) {
            //@ assume 0 < numCartasMano <= 21;
            puntosMano += obtenerValorCarta(manoJugador[i]);
            i++;
        }
        //@ assert puntosMano >= 2 && puntosMano <= 31;
        return puntosMano;
    }

    public static void main(String[] args) {
        Carta mazo[] = new Carta[] {
            Carta.AS_PICAS, Carta.DOS_PICAS, Carta.TRES_PICAS, Carta.CUATRO_PICAS,
            Carta.CINCO_PICAS, Carta.SEIS_PICAS, Carta.SIETE_PICAS, Carta.OCHO_PICAS,
            Carta.NUEVE_PICAS, Carta.DIEZ_PICAS, Carta.J_PICAS, Carta.Q_PICAS,
            Carta.K_PICAS, Carta.COMODÍN_PICAS, Carta.AS_DIAMANTE, Carta.DOS_DIAMANTE,
            Carta.TRES_DIAMANTE, Carta.CUATRO_DIAMANTE, Carta.CINCO_DIAMANTE, Carta.SEIS_DIAMANTE,
            Carta.SIETE_DIAMANTE, Carta.OCHO_DIAMANTE, Carta.NUEVE_DIAMANTE, Carta.DIEZ_DIAMANTE,
            Carta.J_DIAMANTE, Carta.Q_DIAMANTE, Carta.K_DIAMANTE, Carta.COMODÍN_DIAMANTE,
            Carta.AS_TREBOL, Carta.DOS_TREBOL, Carta.TRES_TREBOL, Carta.CUATRO_TREBOL,
            Carta.CINCO_TREBOL, Carta.SEIS_TREBOL, Carta.SIETE_TREBOL, Carta.OCHO_TREBOL,
            Carta.NUEVE_TREBOL, Carta.DIEZ_TREBOL, Carta.J_TREBOL, Carta.Q_TREBOL,
            Carta.K_TREBOL, Carta.COMODÍN_TREBOL, Carta.AS_CORAZON, Carta.DOS_CORAZON,
            Carta.TRES_CORAZON, Carta.CUATRO_CORAZON, Carta.CINCO_CORAZON, Carta.SEIS_CORAZON,
            Carta.SIETE_CORAZON, Carta.OCHO_CORAZON, Carta.NUEVE_CORAZON, Carta.DIEZ_CORAZON,
            Carta.J_CORAZON, Carta.Q_CORAZON, Carta.K_CORAZON, Carta.COMODÍN_CORAZON
        };

        Carta jugador[] = new Carta[21];
        Carta crupier[] = new Carta[17];
        int crédito = 100;
        int puntosJugador = 0;
        int puntosCrupier = 0;

        Console con = System.console();
        String nombre = con.readLine("Ingrese su nombre: ");
        System.out.println("Es un placer tenerte aqui, " + nombre);
        int apuesta = obtenerApuesta(crédito, con);

        int i = 0;

        while (i < 2) {
            jugador[i] = darCarta(mazo);
            crupier[i] = darCarta(mazo);
            i++;
        }

        puntosJugador = valorMano(jugador, 2);
        puntosCrupier = valorMano(crupier, 2);
        System.out.println("Punto de la carta descubierta del crupier: " + obtenerValorCarta(crupier[0]));
        System.out.println("Puntos actuales: " + puntosJugador);
        String opcion = con.readLine("Escriba cualquier caracter para terminar el juego: ");

    }
}
