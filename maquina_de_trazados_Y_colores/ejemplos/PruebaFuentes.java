import java.awt.Font;

public class PruebaFuentes {

    public static void main(String[] args) {
	MaquinaDeTrazados mt = new MaquinaDeTrazados(700, 200, "Prueba de fuentes", Colores.WHITE);

	mt.dibujarString("Esta es la fuente por defecto", 20, 20);

	mt.configurarFuente("Serif", Font.BOLD, 12);
	mt.dibujarString("Letra Serif de 12 puntos y en negritas", 20, 40);

	mt.configurarFuente("Monospaced", Font.ITALIC, 24);
	mt.dibujarString("Letra Monospaced de 24 puntos y en italicas", 20, 70, Colores.BLUE);

	mt.configurarFuente("SansSerif", Font.PLAIN, 16);
	mt.dibujarString("Letra SansSerif de 16 puntos normal en naranja", 20, 100, Colores.ORANGE);

	mt.configurarFuente("Serif", Font.BOLD + Font.ITALIC, 18);
	mt.dibujarString("Letra Serif de 18 puntos en negritas y en italicas rosadas", 20, 130, Colores.PINK);

	mt.mostrar();
    }
}
