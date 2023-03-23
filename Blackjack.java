import java.util.Random;

public class Blackjack {
    enum Carta {
        AS_PICAS(1, "Picas", "A"),
        DOS_PICAS(2, "Picas", "2"),
        TRES_PICAS(3, "Picas", "3"),
        CUATRO_PICAS(4, "Picas", "4"),
        CINCO_PICAS(5, "Picas", "5"),
        SEIS_PICAS(6, "Picas", "6"),
        SIETE_PICAS(7, "Picas", "7"),
        OCHO_PICAS(8, "Picas", "8"),
        NUEVE_PICAS(9, "Picas", "9"),
        DIEZ_PICAS(10, "Picas", "10"),
        J_PICAS(10, "Picas", "J"),
        Q_PICAS(10, "Picas", "Q"),
        K_PICAS(10, "Picas", "K"),
        COMODIN_PICAS(11, "Picas", "Comodin"),
        AS_DIAMANTE(1, "Diamantes", "A"),
        DOS_DIAMANTE(2, "Diamantes", "2"),
        TRES_DIAMANTE(3, "Diamantes", "3"),
        CUATRO_DIAMANTE(4, "Diamantes", "4"),
        CINCO_DIAMANTE(5, "Diamantes", "5"),
        SEIS_DIAMANTE(6, "Diamantes", "6"),
        SIETE_DIAMANTE(7, "Diamantes", "7"),
        OCHO_DIAMANTE(8, "Diamantes", "8"),
        NUEVE_DIAMANTE(9, "Diamantes", "9"),
        DIEZ_DIAMANTE(10, "Diamantes", "10"),
        J_DIAMANTE(10, "Diamantes", "J"),
        Q_DIAMANTE(10, "Diamantes", "Q"),
        K_DIAMANTE(10, "Diamantes", "K"),
        COMODIN_DIAMANTE(11, "Diamantes", "Comodin"),
        AS_TREBOL(1, "Treboles", "A"),
        DOS_TREBOL(2, "Treboles", "2"),
        TRES_TREBOL(3, "Treboles", "3"),
        CUATRO_TREBOL(4, "Treboles", "4"),
        CINCO_TREBOL(5, "Treboles", "5"),
        SEIS_TREBOL(6, "Treboles", "6"),
        SIETE_TREBOL(7, "Treboles", "7"),
        OCHO_TREBOL(8, "Treboles", "8"),
        NUEVE_TREBOL(9, "Treboles", "9"),
        DIEZ_TREBOL(10, "Treboles", "10"),
        J_TREBOL(10, "Treboles", "J"),
        Q_TREBOL(10, "Treboles", "Q"),
        K_TREBOL(10, "Treboles", "K"),
        COMODIN_TREBOL(11, "Treboles", "Comodin"),
        AS_CORAZON(1, "Corazones", "A"),
        DOS_CORAZON(2, "Corazones", "2"),
        TRES_CORAZON(3, "Corazones", "3"),
        CUATRO_CORAZON(4, "Corazones", "4"),
        CINCO_CORAZON(5, "Corazones", "5"),
        SEIS_CORAZON(6, "Corazones", "6"),
        SIETE_CORAZON(7, "Corazones", "7"),
        OCHO_CORAZON(8, "Corazones", "8"),
        NUEVE_CORAZON(9, "Corazones", "9"),
        DIEZ_CORAZON(10, "Corazones", "10"),
        J_CORAZON(10, "Corazones", "J"),
        Q_CORAZON(10, "Corazones", "Q"),
        K_CORAZON(10, "Corazones", "K"),
        COMODIN_CORAZON(11, "Corazones", "Comodin");

        private final int valor;
        private final String palo, nombre;

        private Carta(int valor, String palo, String nombre) {
            this.valor = valor;
            this.palo = palo;
            this.nombre = nombre;
        }

        public int obtenerValor() {
            return valor;
        }

        public String obtenerPalo() {
            return palo;
        }

        public String obtenerNombre() {
            return nombre;
        }
    }

    public static Carta darCarta(Carta[] baraja) {
        Random carta = new Random();
        int aleatorio = carta.nextInt(56);
        return baraja[aleatorio];
    }

    public static void main(String[] args) {
        Carta mazo[] = Carta.values();
        Carta cartaAleatoria = darCarta(mazo);
        System.out.println(cartaAleatoria);
    }
}
