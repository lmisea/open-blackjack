public class Cartas {
	public static void main(String[] args) {
		int altura = 768;
		int ancho = 1278;

		MaquinaDeTrazados mesa = new MaquinaDeTrazados(ancho, altura, "Mesa de blackjack", Colores.WHITE);

		mesa.dibujarOvaloLleno(1, -(ancho / 2), ancho, ancho, Colores.GREEN);

		// La primera carta del Crupier
		int posXdeCarta = (ancho / 2) - 100;
		int[] xPuntos1 = new int[] { posXdeCarta + 40, posXdeCarta + 50, posXdeCarta + 60, posXdeCarta + 50 };
		int[] yPuntos1 = new int[] { 85, 65, 85, 105 };
		mesa.dibujarRectanguloLleno(posXdeCarta, 10, 100, 150, Colores.WHITE);
		mesa.dibujarRectangulo(posXdeCarta + 8, 20, 82, 130, Colores.DARK_GRAY);
		mesa.dibujarPoligonoLleno(xPuntos1, yPuntos1, 4, Colores.RED);

		mesa.mostrar();
		// Prueba numero 1
		// intento 2
	}
}
